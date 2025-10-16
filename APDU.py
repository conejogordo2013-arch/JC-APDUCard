#!/usr/bin/env python3
"""
JCSimOS - Versión extendida: parser completo + muchos INS "mock" (SELECT, READ/UPDATE,
GET RESPONSE, VERIFY/CHANGE/UNBLOCK, MANAGE CHANNELS, GET/PUT DATA, AUTH, GENERATE AC,
INSTALL/DELETE, PSO, GET CHALLENGE, etc). Sigue siendo single-file, sin persistencia
por defecto. Seguro para experimentación en RAM.

Uso:
  python3 jc_all_in_one_extended.py --mode interactive
  python3 jc_all_in_one_extended.py --mode server --port 9001
  python3 jc_all_in_one_extended.py --mode client --host 127.0.0.1 --port 9001
"""
import argparse
import socket
import socketserver
import threading
import sys
import time
import json

# ---- Status Words ----
SW_OK = bytes([0x90, 0x00])
SW_FILE_NOT_FOUND = bytes([0x6A, 0x82])
SW_WRONG_LENGTH = bytes([0x67, 0x00])
SW_CONDITIONS_NOT_SAT = bytes([0x69, 0x85])
SW_INS_NOT_SUPPORTED = bytes([0x6D, 0x00])
SW_CLA_NOT_SUPPORTED = bytes([0x6E, 0x00])
SW_AUTH_FAILED = bytes([0x63, 0x00])  # will append retries nibble if needed
SW_WRONG_P1P2 = bytes([0x6A, 0x86])
SW_SECURITY_STATUS_NOT_SAT = bytes([0x69, 0x82])
SW_MEMORY_FAILURE = bytes([0x65, 0x81])

# ---- Utilities ----
def hexd(b: bytes):
    return b.hex().upper()

def now_ts():
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())

# ---- APDU parser (short + extended) ----
def parse_apdu(apdu: bytes):
    """
    Returns tuple: (cla, ins, p1, p2, lc, data (bytes), le, raw_remaining)
    lc/le are ints or None. raw_remaining are any trailing bytes after parsed APDU.
    Supports:
      - Case 1: 4 bytes only (no Lc/Le)
      - Case 2s: 4 + 1 (Le short)
      - Case 3s: 4 + 1 + Lc + Data (short)
      - Case 4s: 4 + 1 + Lc + Data + 1 (Le short)
      - Extended: uses 00 + 2-bytes length, etc.
    """
    if len(apdu) < 4:
        raise ValueError("APDU too short")
    cla, ins, p1, p2 = apdu[0], apdu[1], apdu[2], apdu[3]
    idx = 4
    lc = None; data = b''; le = None
    # no more bytes => case 1
    if idx >= len(apdu):
        return cla, ins, p1, p2, lc, data, le, b''
    # read next byte
    b = apdu[idx]
    # If only one trailing byte -> could be Le short (case 2S)
    if len(apdu) == idx + 1:
        le = b if b != 0 else 256
        return cla, ins, p1, p2, lc, data, le, b''
    # if b != 0 -> it's Lc short
    if b != 0:
        lc = b
        idx += 1
        if idx + lc > len(apdu):
            raise ValueError("APDU short for indicated Lc")
        data = apdu[idx: idx+lc]; idx += lc
        if idx < len(apdu):
            # remaining byte(s) -> Le short
            # if exactly one byte left -> short Le
            rem = apdu[idx:]
            if len(rem) == 1:
                le = rem[0] if rem[0] != 0 else 256
                raw_remaining = b''
            else:
                raw_remaining = rem
            return cla, ins, p1, p2, lc, bytes(data), le, raw_remaining
    else:
        # extended
        # need at least 2 more bytes for extended Lc
        if len(apdu) < idx + 3:
            raise ValueError("APDU too short for extended Lc")
        # next two bytes are length
        lc = (apdu[idx+1] << 8) | apdu[idx+2]
        idx += 3
        if idx + lc > len(apdu):
            raise ValueError("APDU short for extended Lc/data")
        data = apdu[idx: idx+lc]; idx += lc
        if idx < len(apdu):
            # try to read extended Le if 2 bytes available
            rem = apdu[idx:]
            if len(rem) in (1,2):
                if len(rem) == 1:
                    le = rem[0] if rem[0] != 0 else 256
                else:
                    le = (rem[0] << 8) | rem[1]
                raw_remaining = b''
            else:
                raw_remaining = rem
            return cla, ins, p1, p2, lc, bytes(data), le, raw_remaining
    return cla, ins, p1, p2, lc, bytes(data), le, b''

# ---- Card Simulator ----
class JCSimCard:
    def __init__(self, max_log=5000):
        # simple file map (AID or fileID as bytes) -> bytearray
        self.files = {
            b'\x6F\x3A': bytearray(b'\x00' * 256),
            b'\x3F\x00': bytearray(b'\x11\x22\x33\x44'),
            b'\x2F\xE2': bytearray(b'EMV_MOCK' + b'\x00'*248)
        }
        # selected AID / file id (bytes)
        self.selected = None
        # logical channels (simple simulation)
        self.channels = {0: {"open": True, "selected": None}}  # ch 0
        self.next_chan = 1
        # PIN/CHV simulation: dict {id: {"value": b'1234', "tries": 3, "max":3, "blocked":False}}
        self.chvs = {
            0: {"value": b'1234', "tries": 3, "max":3, "blocked": False}
        }
        # For GET RESPONSE flows: store last_response_payload when returning 61xx
        self._pending_response = None
        # simple persistent metadata
        self.meta = {
            "atr": b'\x3B\x9F\x95\x80\x1F\xC7\x80\x31\xE0',  # mock ATR
        }
        self.log = []
        self.max_log = max_log
        # GP-like installed applets (AID -> info)
        self.applets = {}
        # simple keys store (label -> key bytes) - mocked, not real crypto
        self.keys = {}
        # store last challenge for authentication
        self._last_challenge = None

    def _log(self, apdu: bytes, resp: bytes):
        self.log.append({"ts": time.time(), "apdu": apdu.hex(), "resp": resp.hex()})
        if len(self.log) > self.max_log:
            self.log.pop(0)

    def dump_log(self):
        for e in self.log:
            print(f"[{time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(e['ts']))}] APDU: {e['apdu']} RESP: {e['resp']}")

    # ---- helpers for SW 63Cx (retries) ----
    def _sw_auth_failed_with_tries(self, tries_left):
        # SW 63Cx where x is number of retries left in hex (0..15). We'll use low nibble.
        x = tries_left & 0x0F
        return bytes([0x63, x])

    # ---- APDU handlers ----
    def process_apdu(self, apdu: bytes) -> bytes:
        try:
            cla, ins, p1, p2, lc, data, le, rem = parse_apdu(apdu)
        except ValueError:
            return SW_WRONG_LENGTH
        # Dispatch by INS
        # SELECT (by AID or by FileID)
        if ins == 0xA4:
            # support by AID (data contains AID) or by FILE ID when Lc==2
            if lc is None:
                return SW_WRONG_LENGTH
            aid = data
            # if file id (2 bytes) and exists
            if len(aid) == 2 and aid in self.files:
                self.selected = aid
                # also set selected in channel 0 by default
                self.channels[0]["selected"] = aid
                return SW_OK
            # if full AID name (try exact match in files or applets)
            if aid in self.files:
                self.selected = aid
                self.channels[0]["selected"] = aid
                return SW_OK
            if aid in self.applets:
                self.selected = aid
                self.channels[0]["selected"] = aid
                return SW_OK
            # not found
            return SW_FILE_NOT_FOUND

        # READ BINARY
        if ins == 0xB0:
            offset = (p1 << 8) | p2
            if not self.selected:
                return SW_FILE_NOT_FOUND
            filedata = self.files.get(self.selected)
            if filedata is None:
                return SW_FILE_NOT_FOUND
            if le is None or le == 0:
                payload = bytes(filedata[offset:])
                return payload + SW_OK
            # bounds safe
            payload = bytes(filedata[offset: offset + le])
            return payload + SW_OK

        # UPDATE BINARY
        if ins == 0xD6:
            if lc is None:
                return SW_WRONG_LENGTH
            offset = (p1 << 8) | p2
            if not self.selected:
                return SW_FILE_NOT_FOUND
            filedata = self.files.get(self.selected)
            if filedata is None:
                return SW_FILE_NOT_FOUND
            if offset + len(data) > len(filedata):
                return SW_WRONG_LENGTH
            filedata[offset: offset+len(data)] = data
            return SW_OK

        # GET RESPONSE (0xC0) - return pending bytes (for 61xx)
        if ins == 0xC0:
            # le indicates max to return
            if not self._pending_response:
                return SW_CONDITIONS_NOT_SAT
            payload = self._pending_response
            if le is None or le == 0:
                tosend = payload
                self._pending_response = None
                return tosend + SW_OK
            tosend = payload[:le]
            left = payload[len(tosend):]
            if left:
                self._pending_response = left
                # indicate still data with 61 xx (we will use 0x61 + len(left))
                # but actual response should be data + 61xx; for simplicity return data + 61xx encoded as SW
                return tosend + bytes([0x61, len(left)])
            else:
                self._pending_response = None
                return tosend + SW_OK

        # GET CHALLENGE (0x84) - return random bytes (mock)
        if ins == 0x84:
            chal = b'\xAA\xBB\xCC\xDD\xEE\x01\x02\x03'  # mock 8 bytes
            self._last_challenge = chal
            return chal + SW_OK

        # VERIFY (0x20) - CHV/PIN
        if ins == 0x20:
            # data contains PIN bytes
            pin = data
            chv = self.chvs.get(0)
            if chv["blocked"]:
                return bytes([0x69, 0x83])  # authentication method blocked
            if pin == chv["value"]:
                chv["tries"] = chv["max"]
                return SW_OK
            else:
                chv["tries"] -= 1
                if chv["tries"] <= 0:
                    chv["blocked"] = True
                    return bytes([0x69, 0x83])
                return self._sw_auth_failed_with_tries(chv["tries"])

        # CHANGE REFERENCE DATA (0x24)
        if ins == 0x24:
            if lc is None or len(data) == 0:
                return SW_WRONG_LENGTH
            chv = self.chvs.get(0)
            # require verify first? for mock, allow change if not blocked
            if chv["blocked"]:
                return bytes([0x69, 0x83])
            chv["value"] = data
            chv["tries"] = chv["max"]
            return SW_OK

        # UNBLOCK/RESET RETRY COUNTER (0x2C) - requires PUK in data (we assume PUK '00000000')
        if ins == 0x2C:
            puk = data
            if puk == b'00000000':
                chv = self.chvs.get(0)
                chv["blocked"] = False
                chv["tries"] = chv["max"]
                return SW_OK
            else:
                return SW_AUTH_FAILED

        # MANAGE CHANNELS (0x70)
        if ins == 0x70:
            # P1: 0x00 open logical channel, 0x80 close
            if p1 == 0x00:
                ch = self.next_chan
                self.channels[ch] = {"open": True, "selected": None}
                self.next_chan += 1
                # return channel number in data (one byte)
                return bytes([ch]) + SW_OK
            elif p1 == 0x80:
                ch_to_close = p2  # use p2 as channel id in mock
                if ch_to_close in self.channels and ch_to_close != 0:
                    self.channels.pop(ch_to_close, None)
                    return SW_OK
                else:
                    return SW_WRONG_P1P2
            else:
                return SW_WRONG_P1P2

        # GET DATA (0xCA) - return metadata or EMV-like data
        if ins == 0xCA:
            tag = (p1 << 8) | p2
            # simple mapping: 0x6F3A -> file bytes if exist
            if bytes([p1, p2]) in self.files:
                payload = bytes(self.files[bytes([p1, p2])][:le if le else None])
                return payload + SW_OK
            # some EMV tag examples
            if tag == 0x9F36:  # ATC mock
                return b'\x00\x01' + SW_OK
            if tag == 0x5A:
                return b'\x41\x42\x43\x44' + SW_OK
            return SW_FILE_NOT_FOUND

        # PUT DATA (0xDA) - store metadata
        if ins == 0xDA:
            # For mock, use p1p2 as key, data as value
            key = f"{p1:02X}{p2:02X}"
            self.meta[key] = data.hex()
            return SW_OK

        # INTERNAL AUTHENTICATE / EXTERNAL AUTHENTICATE / GENERATE AC / COMPUTE MAC (0x88/0x82/0xAE/0x2A)
        if ins in (0x88, 0x82, 0xAE, 0x2A):
            # For mock: validate that we have a last challenge or key, then return dummy mac
            if ins == 0x82:
                # EXTERNAL AUTHENTICATE (host proves to card)
                # Accept anything but require more steps normally
                return SW_OK
            if ins == 0x88:
                # INTERNAL AUTH - card proves to host - return signature mock
                return b'\xDE\xAD\xBE\xEF' + SW_OK
            if ins == 0xAE:
                # GENERATE AC (EMV) - return mocked AC + AIP + AFL simplified
                ac = b'\x01\x02\x03\x04'  # mock cryptogram
                aip = b'\x00\x00'
                afl = b'\x00\x00\x00\x00'
                payload = ac + aip + afl
                return payload + SW_OK
            if ins == 0x2A:
                # PSO (Compute digital signature) mock
                return b'\xFE\xED\xFA\xCE' + SW_OK

        # INSTALL/DELETE (GlobalPlatform-like) - INS: 0xE6 (INSTALL), 0xE4 (DELETE) are examples
        if ins == 0xE6:
            # parse payload: assume first bytes are AID then rest descriptor
            if lc is None or lc < 3:
                return SW_WRONG_LENGTH
            aid = data[:len(data)//2]  # naive split for mock
            self.applets[aid] = {"raw": data.hex()}
            return SW_OK
        if ins == 0xE4:
            # delete by AID in data
            aid = data
            if aid in self.applets:
                self.applets.pop(aid, None)
                return SW_OK
            return SW_FILE_NOT_FOUND

        # GET RESPONSE mock: handled above

        # DEFAULT: unknown ins
        return SW_INS_NOT_SUPPORTED

# ---- TCP Server wrapper (robust framing: \n delimited ASCII hex) ----
class APDUServerHandler(socketserver.BaseRequestHandler):
    def handle(self):
        try:
            buf = b''
            # read until newline (client must send newline after hex)
            self.request.settimeout(2.0)
            while True:
                chunk = self.request.recv(4096)
                if not chunk:
                    break
                buf += chunk
                if b'\n' in buf:
                    lines = buf.split(b'\n')
                    for line in lines[:-1]:
                        line = line.strip()
                        if not line:
                            continue
                        # parse hex text
                        try:
                            apdu = bytes.fromhex(line.decode())
                        except Exception:
                            try:
                                apdu = bytes.fromhex(line.hex())
                            except Exception:
                                self.request.sendall(b"ERR:BADHEX\n")
                                continue
                        resp = self.server.card.process_apdu(apdu)
                        self.server.card._log(apdu, resp)
                        self.request.sendall(resp.hex().encode() + b'\n')
                    buf = lines[-1]
            # handle leftover without newline if any
            if buf:
                try:
                    apdu = bytes.fromhex(buf.decode())
                    resp = self.server.card.process_apdu(apdu)
                    self.server.card._log(apdu, resp)
                    self.request.sendall(resp.hex().encode() + b'\n')
                except Exception:
                    self.request.sendall(b"ERR\n")
        except Exception:
            try:
                self.request.sendall(b"ERR\n")
            except:
                pass

class APDUServer(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    def __init__(self, server_address, handler_class):
        super().__init__(server_address, handler_class)
        self.card = JCSimCard()

# ---- Simple client helper (TCP) ----
def send_apdu_tcp(hexstr: str, host="127.0.0.1", port=9001, timeout=5.0) -> str:
    """Envía hex string (sin espacios); servidor espera '\n' al final."""
    with socket.create_connection((host, port), timeout=timeout) as s:
        if not hexstr.endswith('\n'):
            hexstr = hexstr + '\n'
        s.sendall(hexstr.encode())
        resp = b''
        while True:
            chunk = s.recv(4096)
            if not chunk:
                break
            resp += chunk
            if b'\n' in resp:
                break
        return resp.strip().decode()

# ---- Interactive local mode (no network) ----
def interactive_mode():
    card = JCSimCard()
    print("Modo interactivo — simulador extendido en memoria.")
    print("Escribe APDUs en HEX (ej: 00A4000C026F3A) o comandos: DUMPLOG, FILES, HELP, EXIT, META, APPLETS")
    while True:
        try:
            line = input("> ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nSaliendo.")
            break
        if not line:
            continue
        cmd = line.upper()
        if cmd == "EXIT":
            break
        if cmd == "HELP":
            print("Comandos: DUMPLOG, FILES, HELP, EXIT, META, APPLETS. O escribe APDU en HEX.")
            continue
        if cmd == "DUMPLOG":
            card.dump_log()
            continue
        if cmd == "FILES":
            print("Files (AID hex : length):")
            for k,v in card.files.items():
                print(f"{k.hex()} : {len(v)} bytes")
            continue
        if cmd == "META":
            print(json.dumps(card.meta, indent=2))
            continue
        if cmd == "APPLETS":
            print("Applets installed (AID hex : raw):")
            for k,v in card.applets.items():
                print(f"{k.hex()}: {v}")
            continue
        # otherwise treat as APDU hex
        try:
            apdu = bytes.fromhex(line)
        except Exception:
            print("BAD HEX. Intenta de nuevo.")
            continue
        resp = card.process_apdu(apdu)
        card._log(apdu, resp)
        # print response: data (hex) and sw1 sw2 (if present)
        if len(resp) >= 2:
            # if last two are SW (common)
            data, sw1, sw2 = resp[:-2], resp[-2], resp[-1]
            # handle special case when response is 61xx as tail bytes (we might have returned 61xx)
            if data and (sw1 == 0x61):
                # 61 xx returned as last two bytes -> indicate pending length
                print("DATA:", data.hex(), " SW1 SW2:", f"{sw1:02X} {sw2:02X} (61xx -> more data)")
            else:
                if len(data) == 0:
                    print("SW1 SW2:", f"{sw1:02X} {sw2:02X}")
                else:
                    print("DATA:", data.hex(), " SW1 SW2:", f"{sw1:02X} {sw2:02X}")
        else:
            print("RESP:", resp.hex())

# ---- Simple client test sequence ----
def client_mode(host="127.0.0.1", port=9001):
    tests = [
        ("SELECT EF 6F3A", "00A4000C026F3A"),
        ("READ 4 bytes", "00B0000004"),
        ("WRITE DEADBEEF", "00D6000004DEADBEEF"),
        ("READ 4 bytes", "00B0000004"),
        ("GET CHALLENGE", "0084000008"),
        ("VERIFY (wrong)", "0020000004313233"),
        ("VERIFY (correct)", "0020000004313234"),  # if your pin was 1234 -> adjust
    ]
    for name, hexapdu in tests:
        print("APDU ->", name, hexapdu)
        try:
            resp = send_apdu_tcp(hexapdu, host, port)
            print("RESP ->", resp)
        except Exception as e:
            print("ERROR:", e)
            return

# ---- Main / CLI ----
def main():
    p = argparse.ArgumentParser(description="JCSimOS extended single-file simulator+client.")
    p.add_argument("--mode", choices=["server", "client", "interactive"], default="interactive",
                   help="Modo: server | client | interactive")
    p.add_argument("--host", default="127.0.0.1", help="Host para modo client")
    p.add_argument("--port", type=int, default=9001, help="Port para servidor/client")
    args = p.parse_args()

    if args.mode == "server":
        print(f"Iniciando servidor JCSimOS en 0.0.0.0:{args.port} (CTRL-C para parar)")
        server = APDUServer(("0.0.0.0", args.port), APDUServerHandler)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            print("Servidor detenido.")
            server.shutdown()
            server.server_close()
    elif args.mode == "client":
        client_mode(host=args.host, port=args.port)
    else:
        interactive_mode()

if __name__ == "__main__":
    main()

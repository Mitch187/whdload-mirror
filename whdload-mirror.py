#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Ziel:

- Eine (1) stabile FTP-Verbindung aufbauen.
- Den angegebenen Remote-Ordner rekursiv spiegeln (Ordnerstruktur und Dateien).
- Downloads im Binärmodus durchführen, bei Abbrüchen fortsetzen (Resume/REST).
- Optional Integritätsprüfung per serverseitigem HASH/XCRC (falls vom Server unterstützt).
- Robuste Fehlerbehandlung: Keepalive, Reconnect und Retries bei Timeouts/Netzproblemen.
- Fortschritt, Geschwindigkeit pro Datei und Abschlussstatistik ausgeben.
- Alle Konsolen-Ausgaben zusätzlich in eine datierte Logdatei außerhalb des Zielordners schreiben.
"""

import os
import sys
import ftplib
import time
import zlib
import hashlib
import socket
from posixpath import join as pjoin, normpath
from datetime import datetime, timezone

# ===================== KONFIGURATION =====================
# Alle konfigurierbaren Elemente stehen hier oben zentral und übersichtlich.

# --- SCRIPT-HEADER (Anzeige in Konsole + Log) ---
# Aktiviert die Ausgabe eines Kopfblocks mit Name, Pfaden und Version direkt nach dem Logging-Setup.
HEADER_ENABLED = True  # True: Kopf ausgeben; False: unterdrücken
HEADER_VERSION = "1.0.0"  # Skript-/Build-Version für die Kopfzeile
HEADER_NAME = "WHDLoad Mirror"  # Anzeigename im Kopf (leer -> Dateiname)
HEADER_SHOW_SCRIPT_PATH = True  # True: vollständigen Skriptpfad zusätzlich ausgeben
# --- ENDE SCRIPT-HEADER ---

# Hauptstellschrauben für Ziel, Performance und Stabilität.
FTP_HOST = "ftp2.grandis.nu"  # Ziel-FTP-Server
FTP_PORT = 21  # FTP-Port (Standard: 21)
FTP_USER = "ftp"  # Benutzer (hier: anonym)
FTP_PASS = "any"  # Passwort (hier: anonym)

# Startpunkt der Spiegelung (Leerzeichen erlaubt). Immer als absoluter Pfad behandeln.
REMOTE_PATH = "/Retroplay WHDLoad Packs/Commodore_Amiga_-_WHDLoad_-_Games/"

# Lokaler Zielordner der Spiegelung (Ordner wird bei Bedarf angelegt).
LOCAL_ROOT = "whdload-mirror"

# Verbindungs-/Fehlerverhalten:
USE_PASSIVE = True  # Passivmodus (stabiler hinter NAT/Firewalls)
TIMEOUT = 300  # Großzügiger Timeout für lange Transfers/Idle-Server
MAX_RETRIES = 3  # Wie oft bei Fehlern erneut versuchen
SLEEP_BETWEEN_RETRIES = 2.0  # Wartezeit (s) zwischen Versuchen

# Transfer-Feintuning:
BLOCKSIZE = 1024 * 1024  # 1 MiB-Blöcke -> guter Kompromiss zw. Overhead & Durchsatz
RESUME_PARTIAL = True  # Resume (REST) für abgebrochene Downloads
SKIP_EXISTING_SAME_SIZE = True  # Lokale Datei mit gleicher Größe überspringen
OVERWRITE_DIFFER = False  # Abweichende Größe überschreiben (sonst Resume versuchen)
SET_MTIME = True  # MLSD 'modify' (UTC) als lokales mtime setzen

# Integritätsprüfung:
VERIFY_HASH = "auto"  # "auto": nur, wenn Server HASH/XCRC meldet; True: erzwingen; False: aus
PREFERRED_HASH_ALGOS = ["CRC32", "MD5", "SHA-1", "SHA-256"]  # Geschwindigkeit vor Stärke (CRC32 bevorzugt)

# Anzeige-/Logging-Parameter (nur Ausgabe; keine Wirkung auf echte FTP-Pfade)
# Umschreiben eines führenden Remote-Pfadpräfixes (ein-/ausschaltbar).
DISPLAY_PATH_REWRITE_ENABLED = True  # True: Präfix ersetzen; False: unverändert lassen
DISPLAY_PATH_REWRITE_FROM = "/Retroplay WHDLoad Packs/Commodore_Amiga_-_WHDLoad_-_Games/"  # Präfixquelle
DISPLAY_PATH_REWRITE_TO = "/Retroplay WHDLoad.../"  # Präfixersatz

# Kürzung langer Ausgaben mittels Ellipsis. 0 = keine Kürzung.
DISPLAY_PATH_MAXLEN = 0  # empfohlene Werte: 80..140
DISPLAY_PATH_ELLIPSIS = "middle"  # "left" | "middle" | "right"

def _ellipsize(s: str, maxlen: int, where: str = "middle") -> str:
    """Hilfsfunktion zur Kürzung langer Anzeigetexte für Konsole/Log."""
    if maxlen <= 0 or len(s) <= maxlen:
        return s
    if maxlen <= 3:
        return s[:maxlen]
    where = (where or "middle").lower()
    if where == "left":
        return "…" + s[-(maxlen - 1):]
    if where == "right":
        return s[:maxlen - 1] + "…"
    left = (maxlen - 1) // 2
    right = maxlen - 1 - left
    return s[:left] + "…" + s[-right:]

def format_display_path(remote_path: str) -> str:
    """Formatiert einen Remote-Pfad ausschließlich für Anzeige/Logs, ohne den echten FTP-Pfad zu beeinflussen."""
    try:
        s = str(remote_path)
    except Exception:
        return str(remote_path)
    if DISPLAY_PATH_REWRITE_ENABLED and DISPLAY_PATH_REWRITE_FROM:
        if s.startswith(DISPLAY_PATH_REWRITE_FROM):
            s = DISPLAY_PATH_REWRITE_TO + s[len(DISPLAY_PATH_REWRITE_FROM):]
    if isinstance(DISPLAY_PATH_MAXLEN, int) and DISPLAY_PATH_MAXLEN > 0:
        s = _ellipsize(s, DISPLAY_PATH_MAXLEN, DISPLAY_PATH_ELLIPSIS)
    return s

# ===================== LAUFZEIT-STATUS =====================
# Werte für Abschlussstatistik und Fortschritt.
total_bytes_downloaded = 0  # Summe effektiv übertragener Bytes (ohne "skip")
total_seconds_spent = 0.0  # Summe reiner Transferzeiten (s)
total_files_synced = 0  # Anzahl verarbeiteter Dateien (inkl. "skip")
total_dirs_synced = 0  # Anzahl besuchter/gespiegelter Ordner (inkl. Root)

# Server-Fähigkeiten (wird per FEAT ermittelt):
HASH_SUPPORTED = False  # Unterstützt Server HASH?
HASH_ALGO = None  # Gewählter HASH-Algorithmus via OPTS HASH
XCRC_SUPPORTED = False  # Unterstützt Server XCRC/SITE CRC?

# ===================== LOGGING (Konsole + Datei) =====================
# Spiegeln aller Prints nach stdout/stderr zusätzlich in eine Logdatei (neben LOCAL_ROOT).
class Logger:
    """
    Einfacher Doppel-Writer, der stdout/stderr gleichzeitig an Konsole und Datei schreibt.
    - Vermeidet Umbau des Print-Musters.
    - Flush nach jedem write() -> Logs sind auch bei Abstürzen/Abbrüchen möglichst vollständig.
    """
    def __init__(self, logfile_path: str):
        self.terminal_out = sys.__stdout__
        self.terminal_err = sys.__stderr__
        self.logfile = open(logfile_path, "a", encoding="utf-8")

    def write(self, message: str):
        # Hinweis: Sowohl stdout als auch stderr zeigen hierher.
        self.terminal_out.write(message)
        self.terminal_out.flush()
        self.logfile.write(message)
        self.logfile.flush()

    def flush(self):
        self.terminal_out.flush()
        self.logfile.flush()

def setup_logging():
    """
    Legt Logdatei außerhalb des Zielordners an: YYYY-MM-DD_HH-MM-SS-<LOCAL_ROOT>.log
    und spiegelt stdout/stderr in diese Datei.
    """
    now = datetime.now()
    timestr = now.strftime("%Y-%m-%d_%H-%M-%S")
    logfilename = f"{timestr}-{LOCAL_ROOT}.log"
    base_dir = os.path.abspath(os.path.dirname(LOCAL_ROOT))  # Ordner oberhalb des Zielordners
    os.makedirs(base_dir, exist_ok=True)
    logpath = os.path.join(base_dir, logfilename)
    logger = Logger(logpath)
    sys.stdout = logger
    sys.stderr = logger
    print(f"[INFO] Logging aktiv: {logpath}")

# ===================== SCRIPT-HEADER AUSGABE =====================
def print_script_header(version=None, name=None, show_script_path=None):
    """
    Gibt einen Skriptkopf mit Dateiname, optionalem vollständigen Skriptpfad, Ausführungspfad und Version aus.
    Die Ausgabe erfolgt auf stdout und landet dadurch – nach aktiviertem Logging – auch in der Logdatei.
    """
    # Fallbacks aus globaler Konfiguration (None-Defaults vermeiden NameError zur Definitionszeit)
    version = HEADER_VERSION if version is None else version
    name = HEADER_NAME if name is None else name
    show_script_path = HEADER_SHOW_SCRIPT_PATH if show_script_path is None else show_script_path

    # Skriptpfad robust ermitteln: bevorzugt __file__ (absolut seit Python 3.9), sonst sys.argv
    try:
        script_path = os.path.abspath(__file__)
    except NameError:
        script_path = os.path.abspath(sys.argv) if sys.argv else ""
    script_name = os.path.basename(script_path) if script_path else (name or "script")
    exec_dir = os.getcwd()

    lines = []
    lines.append("=" * 60)
    title = name or script_name
    lines.append(f"Start: {title}")
    lines.append(f"Dateiname: {script_name}")
    if show_script_path and script_path:
        lines.append(f"Dateipfad: {script_path}")
    lines.append(f"Ausführungspfad: {exec_dir}")
    lines.append(f"Version: {version}")
    lines.append("=" * 60)
    print("\n".join(lines))

# ===================== FTP-FUNKTIONEN (Verbindung & Fähigkeiten) =====================
def connect_ftp() -> ftplib.FTP:
    """
    Erstellt eine frische FTP-Verbindung:
    - connect/login
    - Passivmodus
    - Binärmodus (TYPE I)
    - TCP Keepalive (OS-abhängig)
    - Retry bei temporären Fehlern
    """
    last_err = None
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            ftp = ftplib.FTP(timeout=TIMEOUT)  # Timeout auf der Control-Connection
            ftp.connect(FTP_HOST, FTP_PORT, timeout=TIMEOUT)
            ftp.login(FTP_USER, FTP_PASS)
            ftp.set_pasv(USE_PASSIVE)
            # OS-Level Keepalive (optional; nicht überall verfügbar)
            try:
                ftp.sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
            except Exception:
                pass
            # Binärmodus für unveränderte Bytes
            try:
                ftp.voidcmd("TYPE I")
            except Exception:
                pass
            return ftp
        except Exception as e:
            last_err = e
            if attempt < MAX_RETRIES:
                time.sleep(SLEEP_BETWEEN_RETRIES * attempt)
                continue
            # Nach MAX_RETRIES letzten Fehler hochwerfen
            raise last_err

def reconnect_ftp(old_ftp: ftplib.FTP | None) -> ftplib.FTP:
    """Schließt (falls vorhanden) die alte Verbindung, baut eine neue auf und aktualisiert Hash-Fähigkeiten."""
    try:
        if old_ftp:
            try:
                old_ftp.close()
            except Exception:
                pass
    except Exception:
        pass
    new = connect_ftp()
    setup_hash_features(new)
    return new

def keepalive(ftp: ftplib.FTP) -> ftplib.FTP:
    """Sendet NOOP als Keepalive; bei Fehlern wird automatisch neu verbunden."""
    try:
        ftp.voidcmd("NOOP")
        return ftp
    except Exception:
        return reconnect_ftp(ftp)

def setup_hash_features(ftp: ftplib.FTP) -> None:
    """
    Ermittelt per FEAT, ob der Server HASH unterstützt (und mit welchem Algo),
    und ob XCRC/SITE CRC vorhanden ist. Versucht bevorzugten Algo via OPTS HASH zu setzen.
    """
    global HASH_SUPPORTED, HASH_ALGO, XCRC_SUPPORTED
    HASH_SUPPORTED = False
    HASH_ALGO = None
    XCRC_SUPPORTED = False
    try:
        feat = ftp.sendcmd("FEAT")
        lines = [line.strip() for line in feat.splitlines()]
        # HASH-Zeile: listet Algo-Kandidaten (z. B. "SHA-256;SHA-512;SHA-1;MD5;CRC32")
        hash_line = next((ln for ln in lines if ln.upper().startswith("HASH")), None)
        if hash_line:
            tokens = hash_line.split()
            algos = []
            if len(tokens) >= 2:
                for part in tokens[1].split(";"):
                    algos.append(part.replace("*", "").strip())
            for pref in PREFERRED_HASH_ALGOS:
                if pref in algos:
                    try:
                        ftp.sendcmd(f"OPTS HASH {pref}")
                        HASH_SUPPORTED = True
                        HASH_ALGO = pref
                        break
                    except Exception:
                        continue
        # XCRC/SITE CRC erkennen (nicht standardisiert, aber verbreitet)
        if any("XCRC" in ln.upper() for ln in lines) or any("SITE" in ln.upper() and "CRC" in ln.upper() for ln in lines):
            XCRC_SUPPORTED = True
    except Exception:
        pass

# ===================== LISTING- & HILFSFUNKTIONEN =====================
def ensure_local_dir(path: str) -> None:
    """Erzeugt ein lokales Verzeichnis idempotent (kein Fehler, wenn es existiert)."""
    os.makedirs(path, exist_ok=True)

def parse_modify_to_epoch(modify: str) -> float:
    """Wandelt MLSD 'modify' (YYYYMMDDHHMMSS, UTC) in POSIX-Timestamp um."""
    dt = datetime.strptime(modify, "%Y%m%d%H%M%S").replace(tzinfo=timezone.utc)
    return dt.timestamp()

def local_hash(path: str, algo: str) -> str:
    """
    Berechnet die lokale Prüfsumme effizient:
    - CRC32 via zlib (sehr schnell)
    - sonst hashlib (MD5/SHA-Varianten)
    """
    algo_norm = algo.replace("-", "").lower()
    if algo_norm == "crc32":
        crc = 0
        with open(path, "rb") as f:
            while True:
                chunk = f.read(1024 * 1024)
                if not chunk:
                    break
                crc = zlib.crc32(chunk, crc)
        return f"{crc & 0xFFFFFFFF:08x}"
    else:
        h = hashlib.new(algo_norm)
        with open(path, "rb") as f:
            while True:
                chunk = f.read(1024 * 1024)
                if not chunk:
                    break
                h.update(chunk)
        return h.hexdigest()

def try_cwd_is_dir(ftp: ftplib.FTP, name: str) -> bool:
    """
    Prüft via CWD-Test, ob 'name' (im aktuellen Verzeichnis) ein Ordner ist.
    Sicherer Fallback, wenn MLSD 'type' unklar ist.
    """
    cur = None
    try:
        cur = ftp.pwd()
        ftp.cwd(name)
        if cur:
            ftp.cwd(cur)
        return True
    except Exception:
        try:
            if cur:
                ftp.cwd(cur)
        except Exception:
            pass
        return False

def list_entries(ftp: ftplib.FTP, remote_dir: str):
    """
    Robustes Listing:
    - Hält Steuerverbindung per NOOP frisch (Keepalive).
    - Bevorzugt MLSD (liefert type/size/modify), weil maschinenlesbar.
    - Fällt auf NLST + CWD-Test zurück, wenn MLSD nicht verfügbar ist.
    - Reduziert CWD/PWD-Wechsel, um Timeout-Risiken zu minimieren.
    """
    ftp = keepalive(ftp)
    for attempt in range(1, MAX_RETRIES + 1):
        cur = None
        try:
            try:
                cur = ftp.pwd()
            except Exception:
                ftp = reconnect_ftp(ftp)
                cur = None
            ftp.cwd(remote_dir)
            items = []
            try:
                for name, facts in ftp.mlsd():
                    if name in (".", ".."):
                        continue
                    t = (facts.get("type") or "").lower()
                    if t in ("dir", "cdir", "pdir"):
                        items.append((name, "dir", facts))
                    elif t == "file":
                        items.append((name, "file", facts))
                    else:
                        if try_cwd_is_dir(ftp, name):
                            items.append((name, "dir", facts))
                        else:
                            items.append((name, "file", facts))
                return items
            except Exception:
                # MLSD schlug fehl -> Fallback NLST + CWD-Test
                try:
                    names = ftp.nlst()
                except Exception:
                    names = []
                items = []
                for name in names:
                    if name in (".", ".."):
                        continue
                    if try_cwd_is_dir(ftp, name):
                        items.append((name, "dir", {}))
                    else:
                        items.append((name, "file", {}))
                return items
        except Exception:
            # Verbindung erneuern und erneut versuchen
            ftp = reconnect_ftp(ftp)
            time.sleep(SLEEP_BETWEEN_RETRIES)
        finally:
            if cur:
                try:
                    ftp.cwd(cur)
                except Exception:
                    pass
    return []  # nach MAX_RETRIES lieber leere Liste als Abbruch

def remote_file_size(ftp: ftplib.FTP, remote_path: str, facts: dict | None) -> int | None:
    """
    Liefert Dateigröße:
    - 1) Aus MLSD-Fakten (sofern vorhanden).
    - 2) SIZE mit absolutem Pfad (vermeidet PWD/CWD, stabiler auf wackeligen Steuerkanälen).
    - 3) Falls alles scheitert: None (wir verlassen uns dann auf Transfer/Verifikation).
    """
    # 1) MLSD-Fakten nutzen
    if facts:
        size = facts.get("size") or facts.get("sizd")
        if size and str(size).isdigit():
            return int(size)
    # 2) SIZE absolut
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            try:
                ftp.voidcmd("TYPE I")  # manche Server verlangen TYPE I vor SIZE
            except Exception:
                pass
            return ftp.size(remote_path)  # viele Server akzeptieren absolute Pfade direkt
        except Exception:
            ftp = reconnect_ftp(ftp)
            time.sleep(SLEEP_BETWEEN_RETRIES)
    # 3) Keine Größe ermittelbar
    return None

def server_hash(ftp: ftplib.FTP, remote_path: str):
    """
    Holt serverseitige Prüfsumme (Referenz):
    - Bevorzugt HASH (mit zuvor via OPTS HASH gewähltem Algo)
    - Fallback XCRC/SITE CRC (meist CRC32)
    - Wenn beides fehlt, (None, None)
    """
    if HASH_SUPPORTED and HASH_ALGO:
        try:
            resp = ftp.sendcmd(f"HASH {remote_path}")
            parts = resp.strip().split()
            hexdig = None
            for tok in reversed(parts):
                if all(c in "0123456789abcdefABCDEF" for c in tok):
                    hexdig = tok.lower()
                    break
            if hexdig:
                return (HASH_ALGO, hexdig)
        except Exception:
            pass
    if XCRC_SUPPORTED:
        try:
            try:
                resp = ftp.sendcmd(f"XCRC {remote_path}")
            except Exception:
                resp = ftp.sendcmd(f"SITE CRC {remote_path}")
            parts = resp.strip().split()
            hexdig = None
            for tok in reversed(parts):
                if all(c in "0123456789abcdefABCDEF" for c in tok):
                    hexdig = tok.lower()
                    break
            if hexdig:
                return ("CRC32", hexdig)
        except Exception:
            pass
    return (None, None)

# ===================== DOWNLOAD =====================
def _download_and_verify(ftp: ftplib.FTP, remote_path: str, local_path: str, facts: dict | None):
    """
    Kerntransfer mit Zeitmessung und optionaler Verifikation:
    - Resume ab lokaler Größe (REST), falls sinnvoll.
    - Bei Fehlern: Reconnect + Retry.
    - Bei Hash-Mismatch: einmaliger Voll-Reload ohne Resume, danach erneute Verifikation.
    - Setzt optional mtime aus MLSD 'modify'.
    """
    l_exists = os.path.exists(local_path)
    l_size = os.path.getsize(local_path) if l_exists else 0
    action = "downloaded"
    bytes_dl = 0  # Download-Zähler

    # Resume-Entscheidung
    if RESUME_PARTIAL and l_exists and l_size > 0:
        rest = l_size
        mode = "ab"
        action = "resumed"
    else:
        rest = None
        mode = "wb"

    tmp_path = local_path + (".part" if rest is None else "")

    # Sauberer Neu-Download: alte .part-Datei beseitigen
    if rest is None and os.path.exists(tmp_path):
        try:
            os.remove(tmp_path)
        except Exception:
            pass

    t0 = time.perf_counter()

    # Transfer mit Reconnect/Retries
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            with open(tmp_path if rest is None else local_path, mode) as f:
                def write_chunk(chunk: bytes):
                    nonlocal bytes_dl
                    f.write(chunk)
                    bytes_dl += len(chunk)
                if rest is not None and rest > 0:
                    ftp.retrbinary(f"RETR {remote_path}", write_chunk, blocksize=BLOCKSIZE, rest=rest)
                else:
                    ftp.retrbinary(f"RETR {remote_path}", write_chunk, blocksize=BLOCKSIZE)
            break
        except Exception:
            ftp = reconnect_ftp(ftp)
            if attempt >= MAX_RETRIES:
                raise
            time.sleep(SLEEP_BETWEEN_RETRIES)

    t1 = time.perf_counter()
    secs = max(t1 - t0, 1e-6)

    # Abschlussbehandlung für Neu-Download
    if rest is None:
        if OVERWRITE_DIFFER and os.path.exists(local_path):
            try:
                os.remove(local_path)
            except Exception:
                pass
        os.replace(tmp_path, local_path)

    mbps = (bytes_dl / (1024 * 1024)) / secs

    # Integrität prüfen (nur wenn Server Referenz liefert; ansonsten "SIZE_ONLY")
    verify = "SIZE_ONLY"
    algo, remote_hex = server_hash(ftp, remote_path)
    if algo and remote_hex and os.path.exists(local_path):
        local_hex = local_hash(local_path, algo)
        if local_hex.lower() == remote_hex.lower():
            verify = f"OK ({algo})"
        else:
            # Einmaliger Voll-Reload ohne Resume + erneute Verifikation
            verify = f"FAIL ({algo}) - wird neu geladen"
            try:
                os.remove(local_path)
            except Exception:
                pass

            t0b = time.perf_counter()
            bytes_dl2 = 0
            for attempt in range(1, MAX_RETRIES + 1):
                try:
                    tmp2 = local_path + ".part"
                    if os.path.exists(tmp2):
                        try:
                            os.remove(tmp2)
                        except Exception:
                            pass
                    with open(tmp2, "wb") as f2:
                        def write_chunk2(chunk: bytes):
                            nonlocal bytes_dl2
                            f2.write(chunk)
                            bytes_dl2 += len(chunk)
                        ftp.retrbinary(f"RETR {remote_path}", write_chunk2, blocksize=BLOCKSIZE)
                    os.replace(tmp2, local_path)
                    break
                except Exception:
                    ftp = reconnect_ftp(ftp)
                    if attempt >= MAX_RETRIES:
                        raise
                    time.sleep(SLEEP_BETWEEN_RETRIES)

            t1b = time.perf_counter()
            secs2 = max(t1b - t0b, 1e-6)
            mbps = bytes_dl2 / (1024 * 1024) / secs2
            local_hex2 = local_hash(local_path, algo)
            if local_hex2.lower() == remote_hex.lower():
                verify = f"OK ({algo})"
                action = "re-downloaded"
                bytes_dl = bytes_dl2
                secs = secs2
            else:
                verify = f"FAIL ({algo})"

    # Optional mtime setzen (nur wenn MLSD 'modify' geliefert hat)
    if SET_MTIME and facts and facts.get("modify") and os.path.exists(local_path):
        try:
            ts = parse_modify_to_epoch(facts["modify"])
            os.utime(local_path, (ts, ts))
        except Exception:
            pass

    return {"action": action, "bytes": bytes_dl, "secs": secs, "mbps": mbps, "verify": verify}

def download_file(ftp: ftplib.FTP, remote_path: str, local_path: str, facts: dict | None):
    """
    Wrapper um _download_and_verify mit Skip-/Resume-/Statistik-Logik:
    - Prüft optional Größe (Skip) und Hash (bei Skip ggf. trotzdem schnell verifizieren).
    - Hält Steuerverbindung vor/nach dem Transfer via NOOP frisch.
    - Aktualisiert globale Statistikzähler.
    """
    global total_bytes_downloaded, total_seconds_spent, total_files_synced

    # Steuerverbindung am Leben halten (Idle-Timeouts vermeiden)
    ftp = keepalive(ftp)

    try:
        ftp.voidcmd("TYPE I")
    except Exception:
        pass

    r_size = remote_file_size(ftp, remote_path, facts)
    l_exists = os.path.exists(local_path)
    l_size = os.path.getsize(local_path) if l_exists else 0

    stats = {"action": "none", "bytes": 0, "secs": 0.0, "mbps": 0.0, "verify": "SKIPPED"}

    # Skip bei gleicher Größe (optional trotzdem Referenz-Hash prüfen)
    if SKIP_EXISTING_SAME_SIZE and l_exists and r_size is not None and l_size == r_size:
        stats["action"] = "skipped_same_size"
        algo, remote_hex = server_hash(ftp, remote_path)
        if algo and remote_hex:
            local_hex = local_hash(local_path, algo)
            if local_hex.lower() == remote_hex.lower():
                stats["verify"] = f"OK ({algo})"
            else:
                stats["verify"] = f"FAIL ({algo}) - wird neu geladen"
                try:
                    os.remove(local_path)
                except Exception:
                    pass
                stats = _download_and_verify(ftp, remote_path, local_path, facts)
        else:
            stats["verify"] = "SIZE_ONLY"

        total_files_synced += 1
        ftp = keepalive(ftp)
        return stats

    # Normaler Download
    stats = _download_and_verify(ftp, remote_path, local_path, facts)
    total_bytes_downloaded += stats["bytes"]
    total_seconds_spent += stats["secs"]
    total_files_synced += 1

    # Größen-Postcheck (falls Größe bekannt)
    if r_size is not None and os.path.exists(local_path):
        if os.path.getsize(local_path) != r_size:
            try:
                os.remove(local_path)
            except Exception:
                pass
            raise IOError("Size mismatch")

    ftp = keepalive(ftp)
    return stats

# ===================== SPIEGELUNG (REKURSIV) =====================
def mirror_dir(ftp: ftplib.FTP, base_remote: str, base_local: str) -> None:
    """
    Rekursive Spiegelung des Remote-Baums:
    - Erst Ordner anlegen/absteigen, dann Dateien laden.
    - Pro Verzeichnis/Datei Fortschritt ausgeben.
    - Zählt Ordner/Dateien für Abschlussstatistik mit.
    """
    global total_dirs_synced

    base_remote = normpath("/" + base_remote.lstrip("/"))
    ensure_local_dir(base_local)

    def recurse(remote_dir: str):
        global total_dirs_synced  # WICHTIG: globale Zählvariable binden, bevor sie verändert wird

        # Ordnerzählung (inkl. Root-Ebene)
        total_dirs_synced += 1

        # Lokaler Zielpfad für remote_dir
        rel = remote_dir[len(base_remote):].lstrip("/") if remote_dir.startswith(base_remote) else remote_dir.lstrip("/")
        local_dir = os.path.join(base_local, rel) if rel else base_local
        ensure_local_dir(local_dir)

        print(f"[DIR] {format_display_path(remote_dir)}")

        # Verbindungs-Check & Listing
        cur_ftp = keepalive(ftp)
        retries = 0
        while True:
            try:
                entries = list_entries(cur_ftp, remote_dir)
                break
            except Exception as e:
                retries += 1
                if retries >= MAX_RETRIES:
                    print(f"[WARN] Listing fehlgeschlagen in '{format_display_path(remote_dir)}': {e}")
                    return
                cur_ftp = reconnect_ftp(cur_ftp)
                time.sleep(SLEEP_BETWEEN_RETRIES)

        # Trenne in Ordner und Dateien
        dirs = [(n, f) for (n, t, f) in entries if t == "dir"]
        files = [(n, f) for (n, t, f) in entries if t == "file"]

        # Zuerst Unterordner (Tiefe zuerst)
        for name, facts in dirs:
            next_remote = normpath(pjoin(remote_dir, name))
            next_local = os.path.join(local_dir, name)
            ensure_local_dir(next_local)
            recurse(next_remote)

        # Danach Dateien im aktuellen Ordner
        for name, facts in files:
            r_path = normpath(pjoin(remote_dir, name))
            l_path = os.path.join(local_dir, name)
            size_str = ""
            r_size = remote_file_size(cur_ftp, r_path, facts)
            if r_size is not None:
                size_str = f" ({r_size / (1024 * 1024):.2f} MiB)"
            print(f"[FILE] {format_display_path(r_path)}{size_str} ...", end=" ")
            try:
                stats = download_file(cur_ftp, r_path, l_path, facts)
                print(f"-> {stats['action']}; {stats['bytes'] / (1024 * 1024):.2f} MiB in {stats['secs']:.2f}s @ {stats['mbps']:.2f} MB/s; VERIFY: {stats['verify']}")
            except Exception as e:
                print(f"[WARN] Download fehlgeschlagen: {format_display_path(r_path)} -> {e}")

    # Rekursion ab Basispfad starten
    recurse(base_remote)

# ===================== ABSCHLUSSSTATISTIK =====================
def get_folder_size_gb(directory: str) -> float:
    """Summiert rekursiv die Dateigrößen eines Ordners und gibt GB (GiB) zurück."""
    total_size = 0
    for root, dirs, files in os.walk(directory):
        for f in files:
            try:
                fp = os.path.join(root, f)
                total_size += os.path.getsize(fp)
            except Exception:
                pass
    return total_size / (1024 ** 3)

# ===================== MAIN =====================
def main():
    # Frühes Logging, damit alle Ausgaben ab hier in der Logdatei landen.
    setup_logging()

    # Kopf sofort nach aktivem Logging ausgeben (geht in Konsole + Log)
    if HEADER_ENABLED:
        print_script_header()

    print(f"Starte FTP-Spiegelung von '{FTP_HOST}' ab '{format_display_path(REMOTE_PATH)}'")
    start_time = datetime.now()
    print(f"Startzeit: {start_time.strftime('%Y-%m-%d %H:%M:%S')}")

    ftp = connect_ftp()
    try:
        setup_hash_features(ftp)  # Ermittelt HASH/XCRC-Unterstützung einmalig
        start_path = normpath("/" + REMOTE_PATH.lstrip("/"))
        mirror_dir(ftp, start_path, LOCAL_ROOT)
    finally:
        # Verbindung stets sauber beenden
        try:
            ftp.quit()
        except Exception:
            try:
                ftp.close()
            except Exception:
                pass

    # Abschlussstatistik
    end_time = datetime.now()
    print(f"\n")
    duration = end_time - start_time
    hours, remainder = divmod(duration.total_seconds(), 3600)
    minutes, _ = divmod(remainder, 60)
    avg_mbps = total_bytes_downloaded / (1024 * 1024) / total_seconds_spent if total_seconds_spent > 0 else 0.0

    print("===== Zusammenfassung =====")
    print(f"Startzeit: {start_time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Endzeit: {end_time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Dauer: {int(hours)} Stunden {int(minutes)} Minuten")
    print(f"Ordner gesamt: {total_dirs_synced}")
    print(f"Dateien gesamt: {total_files_synced}")
    print(f"Gesamtdownload: {total_bytes_downloaded / (1024 * 1024):.2f} MiB")
    print(f"Ø Downloadrate: {avg_mbps:.2f} MB/s")
    folder_size_gb = get_folder_size_gb(LOCAL_ROOT)
    print(f"Belegter Speicher im Ziel '{LOCAL_ROOT}': {folder_size_gb:.2f} GB")
    print("===========================")

if __name__ == "__main__":
    main()

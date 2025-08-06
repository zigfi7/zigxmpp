#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import asyncio
import base64
import hashlib
import logging
import os
import secrets
import ssl
import sys
import uuid
import xml.etree.ElementTree as ET
import zlib
import json
import mimetypes
import ipaddress
import time
import re
import argparse
from dataclasses import dataclass, asdict, field
from datetime import datetime, timezone, timedelta
from enum import Enum, auto
from pathlib import Path
from typing import Dict, Optional, Set, Tuple, List, Any

try:
  from aiohttp import web
  import aiofiles
  import aiofiles.os
  from cryptography import x509
  from cryptography.x509.oid import NameOID
  from cryptography.hazmat.primitives import hashes, serialization
  from cryptography.hazmat.primitives.asymmetric import rsa
  from PIL import Image
except ImportError:
  print("Error: Required libraries are missing.", file=sys.stderr)
  print("Please install them via: pip install aiohttp aiofiles cryptography Pillow", file=sys.stderr)
  sys.exit(1)

DEFAULT_CONFIG = {
  'domain': 'zigxmpp.lan',
  'host': '0.0.0.0',
  'xmpp_port': 5222,
  'xmpp_tls_port': 5223,
  'http_port': 8222,
  'users_file': 'users.txt',
  'data_dir': './data',
  'upload_dir': './uploads',
  'cert_file': 'server.crt',
  'key_file': 'server.key',
  'log_level': 'INFO',
  'allow_in_band_registration': True,
  'upload_limit_mb': 50,
  'upload_ttl_hours': 24,
  'server_name': 'ZigXMPP',
  'server_version': '7.4-DiscoFix',
  'max_file_size_mb': 100,
  'allowed_file_types': ['image/jpeg', 'image/png', 'image/gif', 'text/plain', 'application/pdf'],
  'max_files_per_user': 100,
  'generate_thumbnails': True,
  'thumbnail_size': (200, 200),
  'require_auth_for_download': False
}

NS = {
  'stream': 'http://etherx.jabber.org/streams', 'client': 'jabber:client',
  'sasl': 'urn:ietf:params:xml:ns:xmpp-sasl', 'tls': 'urn:ietf:params:xml:ns:xmpp-tls',
  'bind': 'urn:ietf:params:xml:ns:xmpp-bind', 'roster': 'jabber:iq:roster',
  'compress': 'http://jabber.org/protocol/compress', 'register': 'jabber:iq:register',
  'ping': 'urn:xmpp:ping', 'session': 'urn:ietf:params:xml:ns:xmpp-session',
  'disco_info': 'http://jabber.org/protocol/disco#info',
  'disco_items': 'http://jabber.org/protocol/disco#items',
  'upload': 'urn:xmpp:http:upload:0', 'vcard': 'vcard-temp',
  'last': 'jabber:iq:last', 'private': 'jabber:iq:private',
  'mam_2': 'urn:xmpp:mam:2', 'rsm': 'http://jabber.org/protocol/rsm',
  'caps': 'http://jabber.org/protocol/caps',
  'stream_errors': 'urn:ietf:params:xml:ns:xmpp-streams',
  'stanzas_errors': 'urn:ietf:params:xml:ns:xmpp-stanzas',
  'receipts': 'urn:xmpp:receipts', 'time': 'urn:xmpp:time:0',
  'version': 'jabber:iq:version', 'carbons': 'urn:xmpp:carbons:2',
  'forward': 'urn:xmpp:forward:0', 'delay': 'urn:xmpp:delay',
  'sm': 'urn:xmpp:sm:3', 'blocking': 'urn:xmpp:blocking',
  'muc': 'http://jabber.org/protocol/muc',
  'muc_user': 'http://jabber.org/protocol/muc#user',
  'chatstates': 'http://jabber.org/protocol/chatstates',
  'data': 'jabber:x:data'
}
for prefix, uri in NS.items(): ET.register_namespace(prefix.replace('_', '-'), uri)

JID_REGEX = re.compile(r"^(?:([^@/]+)@)?([^@/]+)(?:/([^@/]+))?$")

@dataclass
class User:
  uuid: str
  username: str
  password_hash: str
  salt: str
  created_at: datetime
  vcard: Optional[str] = None
  last_activity: Optional[datetime] = None
  last_presence: Optional[str] = None
  carbons_enabled: bool = False

@dataclass
class ArchiveMessage:
  id: str
  owner_jid: str
  with_jid: str
  stanza: str
  timestamp: datetime

@dataclass
class FileUpload:
  id: str
  filename: str
  filepath: str
  uploader_jid: str
  file_size: int
  content_type: str
  uploaded_at: datetime
  file_hash: str = ""
  thumbnail_path: Optional[str] = None
  download_count: int = 0
  access_list: List[str] = field(default_factory=list)
  expires_at: Optional[datetime] = None

@dataclass
class JID:
  username: str
  domain: str
  resource: Optional[str] = None

  @classmethod
  def from_string(cls, jid_str: str) -> Optional['JID']:
    if not jid_str: return None
    match = JID_REGEX.match(jid_str)
    if not match: return None
    username, domain, resource = match.groups()
    return cls(username or '', domain, resource)

  def __str__(self):
    base = f"{self.username}@{self.domain}" if self.username else self.domain
    return f"{base}/{self.resource}" if self.resource else base

  def bare(self) -> str:
    return f"{self.username}@{self.domain}" if self.username else self.domain

class State(Enum):
  INIT = auto(); TLS_NEGOTIATED = auto(); COMPRESSED = auto()
  AUTHENTICATED = auto(); BOUND = auto()

class SimpleDB:
  def __init__(self, data_dir: Path):
    self.data_dir = data_dir
    self.users_file = data_dir / 'users.json'
    self.uploads_file = data_dir / 'uploads.json'
    self.offline_file = data_dir / 'offline.json'
    self.archive_file = data_dir / 'archive.json'
    self._users: Dict[str, User] = {}
    self._users_by_name: Dict[str, str] = {}
    self._uploads: Dict[str, FileUpload] = {}
    self._offline_messages: Dict[str, List[Dict[str, Any]]] = {}
    self._archive: Dict[str, List[ArchiveMessage]] = {}
    self._lock = asyncio.Lock()

  async def load(self):
    await self._load_data()

  async def _load_data(self):
    async with self._lock:
      self.data_dir.mkdir(parents=True, exist_ok=True)
      if self.users_file.exists():
        try:
          async with aiofiles.open(self.users_file, 'r') as f:
            data = json.loads(await f.read())
            for uuid_val, user_data in data.items():
              user_data['created_at'] = datetime.fromisoformat(user_data['created_at'])
              if user_data.get('last_activity'): user_data['last_activity'] = datetime.fromisoformat(user_data['last_activity'])
              self._users[uuid_val] = User(**user_data)
              self._users_by_name[user_data['username']] = user_data['username']
        except Exception as e:
          logger.error(f"Error loading users from {self.users_file}: {e}")
      if self.uploads_file.exists():
        try:
          async with aiofiles.open(self.uploads_file, 'r') as f:
            data = json.loads(await f.read())
            for k, v in data.items():
              v['uploaded_at'] = datetime.fromisoformat(v['uploaded_at'])
              if v.get('expires_at'): v['expires_at'] = datetime.fromisoformat(v['expires_at'])
              self._uploads[k] = FileUpload(**v)
        except Exception as e:
          logger.error(f"Error loading uploads from {self.uploads_file}: {e}")
      if self.offline_file.exists():
        try:
          async with aiofiles.open(self.offline_file, 'r') as f:
            self._offline_messages = json.loads(await f.read())
        except Exception as e:
          logger.error(f"Error loading offline messages from {self.offline_file}: {e}")
      if self.archive_file.exists():
        try:
          async with aiofiles.open(self.archive_file, 'r') as f:
            data = json.loads(await f.read())
            for owner, msgs in data.items():
              self._archive[owner] = [ArchiveMessage(**{**m, 'timestamp': datetime.fromisoformat(m['timestamp'])}) for m in msgs]
        except Exception as e:
          logger.error(f"Error loading archive from {self.archive_file}: {e}")

  async def _save_data(self, file_path: Path, data: Any):
    async with self._lock:
      try:
        temp_path = file_path.with_suffix('.tmp')
        async with aiofiles.open(temp_path, 'w') as f:
          await f.write(json.dumps(data, indent=2))
        os.replace(temp_path, file_path)
      except Exception as e:
        logger.error(f"Error saving data to {file_path}: {e}")

  async def save_users(self):
    data = {}
    for k, v in self._users.items():
      user_dict = asdict(v)
      user_dict['created_at'] = v.created_at.isoformat()
      if v.last_activity: user_dict['last_activity'] = v.last_activity.isoformat()
      data[k] = user_dict
    await self._save_data(self.users_file, data)

  async def get_user(self, username: str) -> Optional[User]:
    async with self._lock:
      user_uuid = self._users_by_name.get(username)
      return self._users.get(user_uuid) if user_uuid else None

  async def update_user(self, user: User):
    async with self._lock:
      self._users[user.uuid] = user
    await self.save_users()

  async def create_user(self, username: str, password: str) -> bool:
    async with self._lock:
      if username in self._users_by_name: return False
      user_uuid = str(uuid.uuid4())
      salt = secrets.token_hex(16)
      pwd_hash = hashlib.pbkdf2_hmac('sha256', password.encode(), salt.encode(), 260000).hex()
      user = User(uuid=user_uuid, username=username, password_hash=pwd_hash, salt=salt, created_at=datetime.now(timezone.utc))
      self._users[user_uuid] = user
      self._users_by_name[username] = user_uuid
    await self.save_users()
    return True

  async def get_all_users(self) -> List[User]:
    async with self._lock:
      return list(self._users.values())

  async def save_upload(self, upload: FileUpload):
    async with self._lock:
      if upload:
        self._uploads[upload.id] = upload
    
    def json_default(o):
      if isinstance(o, datetime):
        return o.isoformat()
      return o

    data_to_save = {k: asdict(v) for k, v in self._uploads.items()}
    await self._save_data(self.uploads_file, json.loads(json.dumps(data_to_save, default=json_default)))

  async def remove_upload(self, upload_id: str):
    async with self._lock:
      self._uploads.pop(upload_id, None)
    await self.save_upload(None)

  async def get_all_uploads(self) -> List[FileUpload]:
    async with self._lock:
      return list(self._uploads.values())

  async def get_upload(self, upload_id: str) -> Optional[FileUpload]:
    async with self._lock:
      return self._uploads.get(upload_id)

  async def add_offline_message(self, to_username: str, msg_elem: ET.Element):
    delay = ET.SubElement(msg_elem, f"{{{NS['delay']}}}delay", {
      'xmlns': NS['delay'], 'from': msg_elem.get('from').split('/')[0],
      'stamp': datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')
    })
    msg_str = ET.tostring(msg_elem, encoding='unicode')
    async with self._lock:
      queue = self._offline_messages.setdefault(to_username, [])
      queue.append({'xml': msg_str})
      if len(queue) > 100:
        self._offline_messages[to_username] = queue[-100:]
    await self._save_data(self.offline_file, self._offline_messages)

  async def get_and_clear_offline_messages(self, username: str) -> List[ET.Element]:
    messages = []
    async with self._lock:
      stored_msgs = self._offline_messages.pop(username, [])
    if stored_msgs:
      for msg_data in stored_msgs:
        try:
          messages.append(ET.fromstring(msg_data['xml']))
        except ET.ParseError as e:
          logger.error(f"Could not parse stored message for {username}: {e}")
      await self._save_data(self.offline_file, self._offline_messages)
    return messages

  async def add_to_archive(self, owner_jid_str: str, with_jid_str: str, stanza: ET.Element):
    stanza_id = stanza.get('id', str(uuid.uuid4()))
    archive_msg = ArchiveMessage(
      id=stanza_id, owner_jid=owner_jid_str, with_jid=with_jid_str,
      stanza=ET.tostring(stanza, encoding='unicode'),
      timestamp=datetime.now(timezone.utc)
    )
    async with self._lock:
      self._archive.setdefault(owner_jid_str, []).append(archive_msg)
    await self._save_data(self.archive_file, {owner: [asdict(m) for m in msgs] for owner, msgs in self._archive.items()})

  async def query_archive(self, owner_jid: str, with_jid: Optional[str] = None, start: Optional[datetime] = None, end: Optional[datetime] = None, before_id: Optional[str] = None, max_results: int = 50) -> Tuple[List[ArchiveMessage], bool]:
    async with self._lock:
      user_archive = sorted(self._archive.get(owner_jid, []), key=lambda m: m.timestamp, reverse=True)
    
    results = []
    start_index = 0
    if before_id:
      try:
        start_index = next(i for i, m in enumerate(user_archive) if m.id == before_id) + 1
      except StopIteration:
        return [], True

    for i in range(start_index, len(user_archive)):
      msg = user_archive[i]
      if with_jid and msg.with_jid != with_jid: continue
      if start and msg.timestamp < start: continue
      if end and msg.timestamp > end: continue
      if len(results) >= max_results: break
      results.append(msg)
      
    complete = (start_index + len(results)) >= len(user_archive)
    return list(reversed(results)), complete

class XMPPProtocol(asyncio.Protocol):
  def __init__(self, server: 'ZigXMPPServer'):
    self.server = server
    self.transport: Optional[asyncio.Transport] = None
    self.peername: Optional[Tuple[str, int]] = None
    self.parser: Optional[ET.XMLPullParser] = None
    self.jid: Optional[JID] = None
    self.user: Optional[User] = None
    self.state = State.INIT
    self.stream_open = False
    self.decompressor: Any = None
    self.compressor: Any = None
    self.depth = 0
    self.session_domain: str = self.server.config['domain']
    self.sm_enabled = False
    self.sm_id: Optional[str] = None
    self.sm_server_handled_count = 0

  def connection_made(self, transport: asyncio.Transport):
    self.transport = transport
    self.peername = transport.get_extra_info('peername')
    if not self.server.allow_connection(self.peername[0]):
      logger.warning(f"Connection from {self.peername} rejected due to IP rate limiting.")
      transport.close()
      return
    logger.info(f"New connection from {self.peername}")
    self.parser = ET.XMLPullParser(['start', 'end'])
    if self.transport.get_extra_info('sslcontext'):
      self.state = State.TLS_NEGOTIATED

  def data_received(self, data: bytes):
    if not self.transport or self.transport.is_closing(): return
    data_to_parse = data
    if self.decompressor:
      try:
        data_to_parse = self.decompressor.decompress(data)
      except zlib.error as e:
        logger.error(f"Decompression error from {self.peername}: {e}"); self.transport.close(); return
    try:
      self.parser.feed(data_to_parse)
      for event, elem in self.parser.read_events():
        if event == 'start':
          self.depth += 1
          if self.depth == 1 and elem.tag == f"{{{NS['stream']}}}stream":
            self.stream_open = True; asyncio.create_task(self.handle_stream_start(elem))
        elif event == 'end':
          self.depth -= 1
          if self.depth == 0 and elem.tag == f"{{{NS['stream']}}}stream":
            logger.info(f"Client {self.peername} closed the stream."); self.transport.close(); return
          elif self.depth == 1 and self.stream_open:
            asyncio.create_task(self.handle_stanza(elem))
    except ET.ParseError as e:
      logger.error(f"XML Parse Error from {self.peername}: {e}")
      asyncio.create_task(self.send_stream_error('xml-not-well-formed', str(e)))
    except Exception as e:
      logger.error(f"Critical error in data_received from {self.peername}: {e}", exc_info=True)
      asyncio.create_task(self.send_stream_error('internal-server-error', 'An unexpected error occurred.'))

  def connection_lost(self, exc: Optional[Exception]):
    logger.info(f"Connection from {self.peername} closed.")
    if self.peername: self.server.release_connection(self.peername[0])
    if self.jid: asyncio.create_task(self.server.handle_disconnect(self))

  async def send_stream_error(self, condition: str, text: Optional[str] = None):
    if not self.transport or self.transport.is_closing(): return
    logger.warning(f"Sending stream error to {self.peername}: {condition}")
    error_elem = ET.Element(f"{{{NS['stream']}}}error")
    ET.SubElement(error_elem, f"{{{NS['stream_errors']}}}{condition}")
    if text: ET.SubElement(error_elem, f"{{{NS['stream_errors']}}}text").text = text
    try:
      await self.send_xml(error_elem); self.transport.write(b'</stream:stream>')
    except Exception as e:
      logger.error(f"Error sending stream error: {e}")
    finally:
      if self.transport and not self.transport.is_closing(): self.transport.close()

  async def handle_stream_start(self, stream_elem: ET.Element):
    client_to_domain = stream_elem.get('to')
    if client_to_domain:
      self.session_domain = client_to_domain
    await self.send_xml(self.server.get_stream_header(self.session_domain, is_response=True))
    features = self.server.get_features_for_state(self.state, self)
    if features is not None: await self.send_xml(features)

  async def handle_stanza(self, elem: ET.Element):
    try:
      self.sm_server_handled_count = (self.sm_server_handled_count + 1) & 0xFFFFFFFF
      if elem.tag.startswith(f"{{{NS['sm']}}}"):
        return await self.server.handle_sm_stanza(self, elem)
      if self.user:
        self.user.last_activity = datetime.now(timezone.utc); await self.server.db.update_user(self.user)
      local_tag = elem.tag.rpartition('}')[-1]
      handlers = {
        State.BOUND: {"iq": self.server.handle_iq_session, "presence": self.server.handle_presence, "message": self.server.handle_message},
        State.AUTHENTICATED: {"iq": self.server.handle_iq_session},
        State.TLS_NEGOTIATED: {"auth": self.handle_auth, "compress": self.handle_compress, "iq": self.server.handle_iq_pre_auth},
        State.COMPRESSED: {"auth": self.handle_auth, "iq": self.server.handle_iq_pre_auth},
        State.INIT: {"starttls": self.handle_starttls, "iq": self.server.handle_iq_pre_auth},
      }
      handler = handlers.get(self.state, {}).get(local_tag)
      if handler: await handler(self, elem)
      elif local_tag == 'iq' and elem.get('id'): await self.send_xml(self.server.create_iq_error(self, elem, 'cancel', 'feature-not-implemented'))
    except Exception as e:
      logger.error(f"Error handling stanza from {self.peername}: {e}", exc_info=True)

  async def reset_stream(self):
    self.stream_open = False; self.depth = 0
    self.parser = ET.XMLPullParser(['start', 'end'])
    if self.compressor: self.decompressor = zlib.decompressobj()

  async def send_xml(self, data: ET.Element | str):
    if not self.transport or self.transport.is_closing(): return
    try:
      xml_str = ET.tostring(data, encoding='unicode') if isinstance(data, ET.Element) else str(data)
      payload = xml_str.encode('utf-8')
      if self.compressor: payload = self.compressor.compress(payload) + self.compressor.flush(zlib.Z_SYNC_FLUSH)
      self.transport.write(payload)
    except Exception as e:
      logger.error(f"Failed to send XML to {self.peername}: {e}", exc_info=True)

  @staticmethod
  async def handle_starttls(proto, elem=None):
    await proto.send_xml(ET.Element(f"{{{NS['tls']}}}proceed"))
    try:
      new_transport = await asyncio.get_running_loop().start_tls(proto.transport, proto, proto.server.ssl_context, server_side=True)
      proto.transport = new_transport; proto.state = State.TLS_NEGOTIATED
      await proto.reset_stream(); logger.info(f"STARTTLS successful for {proto.peername}")
    except Exception as e:
      logger.error(f"STARTTLS error for {proto.peername}: {e}"); proto.transport.close()

  @staticmethod
  async def handle_compress(proto, elem: ET.Element):
    method_elem = elem.find(f"{{{NS['compress']}}}method")
    if method_elem is not None and method_elem.text == 'zlib':
      await proto.send_xml(ET.Element(f"{{{NS['compress']}}}compressed"))
      proto.compressor = zlib.compressobj(); proto.decompressor = zlib.decompressobj()
      proto.state = State.COMPRESSED; await proto.reset_stream()
      logger.info(f"Stream compression enabled for {proto.peername}")
    else:
      failure = ET.Element(f"{{{NS['compress']}}}failure"); ET.SubElement(failure, 'unsupported-method'); await proto.send_xml(failure)

  @staticmethod
  async def handle_auth(proto, elem: ET.Element):
    user = await proto.server.authenticate_sasl_plain(elem.text)
    if user:
      logger.info(f"Authentication successful for user '{user.username}' from {proto.peername}")
      proto.user = user; user.last_activity = datetime.now(timezone.utc)
      await proto.server.db.update_user(user)
      proto.state = State.AUTHENTICATED; await proto.send_xml(proto.server.get_auth_success()); await proto.reset_stream()
    else:
      logger.warning(f"Authentication failed from {proto.peername}"); await proto.send_xml(proto.server.get_auth_failure()); proto.transport.close()

class SimpleMUC:
  def __init__(self, server: 'ZigXMPPServer'):
    self.server = server
    self.rooms: Dict[str, Dict[str, JID]] = {}

  async def handle_presence(self, from_proto: XMPPProtocol, presence_elem: ET.Element):
    room_jid = JID.from_string(presence_elem.get('to'))
    if not room_jid or not room_jid.username or not room_jid.resource: return
    room_name = room_jid.bare(); nick = room_jid.resource; from_full_jid = str(from_proto.jid)
    is_unavailable = presence_elem.get('type') == 'unavailable'

    if room_name not in self.rooms: self.rooms[room_name] = {}
    occupants = self.rooms[room_name]
    
    for occ_full_jid, _ in list(occupants.items()):
      if occ_full_jid == from_full_jid: continue
      p = ET.fromstring(ET.tostring(presence_elem))
      p.set('from', f"{room_name}/{nick}")
      p.set('to', occ_full_jid)
      x = ET.SubElement(p, f"{{{NS['muc_user']}}}x", {'xmlns': NS['muc_user']})
      ET.SubElement(x, 'item', affiliation='member', role='participant')
      if is_unavailable: ET.SubElement(x, 'status', code='110')
      await self.server.send_to_full_jid(occ_full_jid, p)

    if is_unavailable:
      occupants.pop(from_full_jid, None)
    else:
      for occ_full_jid, occ_room_jid in list(occupants.items()):
        p_other = ET.Element('presence', {'to': from_full_jid, 'from': f"{occ_room_jid.bare()}/{occ_room_jid.resource}"})
        x_other = ET.SubElement(p_other, f"{{{NS['muc_user']}}}x", {'xmlns': NS['muc_user']})
        ET.SubElement(x_other, 'item', affiliation='member', role='participant')
        await from_proto.send_xml(p_other)
      
      occupants[from_full_jid] = room_jid
      p_own = ET.fromstring(ET.tostring(presence_elem))
      p_own.set('from', f"{room_name}/{nick}")
      p_own.set('to', from_full_jid)
      x_own = ET.SubElement(p_own, f"{{{NS['muc_user']}}}x", {'xmlns': NS['muc_user']})
      ET.SubElement(x_own, 'item', affiliation='member', role='participant')
      ET.SubElement(x_own, 'status', code='110')
      ET.SubElement(x_own, 'status', code='201')
      await from_proto.send_xml(p_own)

  async def handle_message(self, from_proto: XMPPProtocol, message_elem: ET.Element):
    room_jid = JID.from_string(message_elem.get('to'))
    if not room_jid or room_jid.bare() not in self.rooms: return
    room_name = room_jid.bare(); occupants = self.rooms[room_name]
    from_full_jid_str = str(from_proto.jid); sender_room_jid = occupants.get(from_full_jid_str)
    if not sender_room_jid: return

    for occupant_full_jid, _ in list(occupants.items()):
      if occupant_full_jid == from_full_jid_str: continue
      msg_copy = ET.fromstring(ET.tostring(message_elem))
      msg_copy.set('from', f"{room_name}/{sender_room_jid.resource}"); msg_copy.set('to', occupant_full_jid)
      await self.server.send_to_full_jid(occupant_full_jid, msg_copy)

class ZigXMPPServer:
  def __init__(self, config):
    self.config = config
    self.muc_domain = f"conference.{config['domain']}"
    self.upload_domain = f"upload.{config['domain']}"
    self.db = SimpleDB(Path(config['data_dir']))
    self.sessions: Dict[str, XMPPProtocol] = {}
    self.user_sessions: Dict[str, Set[str]] = {}
    self.ssl_context: Optional[ssl.SSLContext] = None
    self.upload_slots: Dict[str, Tuple[str, datetime]] = {}
    self.ip_connections: Dict[str, int] = {}
    self.muc = SimpleMUC(self)

  async def setup(self):
    await self.db.load()
    await self.init_users()
    self.generate_self_signed_cert()
    self.ssl_context = ssl.create_default_context(ssl.Purpose.CLIENT_AUTH)
    self.ssl_context.load_cert_chain(self.config['cert_file'], self.config['key_file'])
    Path(self.config['upload_dir']).mkdir(parents=True, exist_ok=True)

  async def init_users(self):
    users_file = Path(self.config['users_file'])
    if not users_file.exists(): return
    logger.info(f"Loading users from {users_file}...")
    async with aiofiles.open(users_file, 'r') as f:
      for line in await f.readlines():
        line = line.strip()
        if line and not line.startswith('#'):
          parts = line.split(maxsplit=1)
          if len(parts) == 2 and not await self.db.get_user(parts[0]):
            if await self.db.create_user(parts[0], parts[1]):
              logger.info(f"Created user from file: {parts[0]}")

  def allow_connection(self, ip: str) -> bool:
    current_connections = self.ip_connections.get(ip, 0)
    if current_connections >= 15: return False
    self.ip_connections[ip] = current_connections + 1
    return True

  def release_connection(self, ip: str):
    if ip in self.ip_connections:
      self.ip_connections[ip] -= 1
      if self.ip_connections[ip] <= 0: del self.ip_connections[ip]

  async def authenticate_sasl_plain(self, auth_text: str) -> Optional[User]:
    if not auth_text: return None
    try:
      decoded = base64.b64decode(auth_text).decode('utf-8')
      if decoded.count('\x00') != 2: return None
      _, username, password = decoded.split('\x00', 2)
      if len(username) > 64 or len(password) > 128: return None
      user = await self.db.get_user(username)
      if not user: return None
      expected_hash = hashlib.pbkdf2_hmac('sha256', password.encode(), user.salt.encode(), 260000).hex()
      return user if secrets.compare_digest(expected_hash, user.password_hash) else None
    except Exception as e:
      logger.error(f"Error during SASL PLAIN authentication: {e}"); return None

  async def handle_iq_bind(self, proto: XMPPProtocol, elem: ET.Element):
    resource = elem.findtext(f".//{{{NS['bind']}}}resource") or f"zig-{secrets.token_hex(4)}"
    proto.jid = JID(proto.user.username, proto.session_domain, resource)
    if await self.register_session(proto): return
    result_iq = self.create_iq_result(proto, elem)
    bind = ET.SubElement(result_iq, f"{{{NS['bind']}}}bind")
    ET.SubElement(bind, f"{{{NS['bind']}}}jid").text = str(proto.jid)
    await proto.send_xml(result_iq)

  async def handle_iq_pre_auth(self, proto: XMPPProtocol, elem: ET.Element):
    query = elem.find("./*")
    if not query: return await proto.send_xml(self.create_iq_error(proto, elem, 'cancel', 'bad-request'))
    if elem.get('type') == 'get' and query.tag == f"{{{NS['disco_info']}}}query":
      return await self.handle_disco_info(proto, elem)
    if self.config['allow_in_band_registration'] and query.tag == f"{{{NS['register']}}}query":
      if elem.get('type') == 'get': return await self.handle_register_get(proto, elem)
      if elem.get('type') == 'set': return await self.handle_register_set(proto, elem)
    await proto.send_xml(self.create_iq_error(proto, elem, 'auth', 'not-authorized'))

  async def handle_iq_session(self, proto: XMPPProtocol, elem: ET.Element):
    if proto.state == State.AUTHENTICATED:
      if elem.find(f"{{{NS['bind']}}}bind") is not None: return await self.handle_iq_bind(proto, elem)
      if elem.find(f"{{{NS['session']}}}session") is not None:
        await proto.send_xml(self.create_iq_result(proto, elem)); return await self.start_client_session(proto)
    if proto.state != State.BOUND:
      return await proto.send_xml(self.create_iq_error(proto, elem, 'auth', 'policy-violation', text='Session not yet established'))
    query = elem.find("./*")
    if query is None: return await proto.send_xml(self.create_iq_error(proto, elem, 'modify', 'bad-request'))
    iq_type = elem.get('type'); query_ns = query.tag.split('}')[0][1:]
    def error(t, n): return lambda p, e: p.send_xml(self.create_iq_error(p, e, t, n))
    handlers = {
      'get': {NS['roster']: self.handle_roster_get, NS['disco_info']: self.handle_disco_info, NS['disco_items']: self.handle_disco_items,
              NS['upload']: self.handle_upload_request, NS['vcard']: self.handle_vcard_get, NS['version']: self.handle_iq_version,
              NS['time']: self.handle_iq_time, NS['last']: self.handle_iq_last, NS['ping']: lambda p, e: p.send_xml(self.create_iq_result(p, e)),
              NS['private']: error('cancel', 'feature-not-implemented'), NS['mam_2']: self.handle_mam_query},
      'set': {NS['roster']: self.handle_roster_set, NS['vcard']: self.handle_vcard_set, NS['carbons']: self.handle_carbons_set,
              NS['private']: lambda p, e: p.send_xml(self.create_iq_result(p, e))}
    }
    handler = handlers.get(iq_type, {}).get(query_ns)
    if handler: return await handler(proto, elem)
    await proto.send_xml(self.create_iq_error(proto, elem, 'cancel', 'service-unavailable'))

  async def start_client_session(self, proto: XMPPProtocol):
    logger.info(f"Session established for {proto.jid}. Now waiting for initial presence.")
    proto.state = State.BOUND

  async def handle_roster_get(self, proto: XMPPProtocol, elem: ET.Element):
    result_iq = self.create_iq_result(proto, elem)
    query_roster = ET.SubElement(result_iq, f"{{{NS['roster']}}}query", {'ver': datetime.now(timezone.utc).isoformat()})
    all_users = await self.db.get_all_users()
    for user in all_users:
      if user.username != proto.user.username:
        ET.SubElement(query_roster, "item", {"jid": f"{user.username}@{proto.session_domain}", "name": user.username, "subscription": "both"})
    await proto.send_xml(result_iq)

  async def handle_roster_set(self, proto: XMPPProtocol, elem: ET.Element):
    logger.debug(f"Ignoring roster set from {proto.jid} due to auto-roster policy.")
    await proto.send_xml(self.create_iq_result(proto, elem))

  async def handle_vcard_get(self, proto: XMPPProtocol, elem: ET.Element):
    target_jid = JID.from_string(elem.get('to', str(proto.jid)))
    if not target_jid: return await proto.send_xml(self.create_iq_error(proto, elem, 'modify', 'bad-request'))
    user_to_fetch = await self.db.get_user(target_jid.username)
    result_iq = self.create_iq_result(proto, elem); result_iq.set('from', target_jid.bare())
    
    vcard_str = user_to_fetch.vcard if user_to_fetch and user_to_fetch.vcard else None
    if not vcard_str:
      vcard_elem = ET.Element(f"{{{NS['vcard']}}}vCard")
      ET.SubElement(vcard_elem, 'FN').text = target_jid.username
      vcard_str = ET.tostring(vcard_elem, encoding='unicode')

    result_iq.append(ET.fromstring(vcard_str))
    await proto.send_xml(result_iq)

  async def handle_vcard_set(self, proto: XMPPProtocol, elem: ET.Element):
    vcard_elem = elem.find(f".//{{{NS['vcard']}}}vCard")
    if vcard_elem is not None:
      proto.user.vcard = ET.tostring(vcard_elem, encoding='unicode'); await self.db.update_user(proto.user)
      await proto.send_xml(self.create_iq_result(proto, elem))
      presence_update = ET.Element('presence')
      if (photo_elem := vcard_elem.find('PHOTO/BINVAL')) is not None and photo_elem.text:
        try:
          photo_hash = hashlib.sha1(base64.b64decode(photo_elem.text)).hexdigest()
          ET.SubElement(presence_update, f"{{{NS['caps']}}}c", {'hash': 'sha-1', 'node': 'http://jabber.org/protocol/caps', 'ver': photo_hash})
        except: pass
      await self.broadcast_to_roster(proto, presence_update)
    else: await proto.send_xml(self.create_iq_error(proto, elem, 'modify', 'bad-request'))

  async def handle_carbons_set(self, proto: XMPPProtocol, elem: ET.Element):
    if elem.find(f".//{{{NS['carbons']}}}enable") is not None: proto.user.carbons_enabled = True
    elif elem.find(f".//{{{NS['carbons']}}}disable") is not None: proto.user.carbons_enabled = False
    await self.db.update_user(proto.user); await proto.send_xml(self.create_iq_result(proto, elem))

  async def handle_disco_info(self, proto: XMPPProtocol, elem: ET.Element):
    to_jid_str = elem.get('to', proto.session_domain); result_iq = self.create_iq_result(proto, elem)
    result_iq.set('from', to_jid_str); query_disco = ET.SubElement(result_iq, f"{{{NS['disco_info']}}}query")
    to_jid = JID.from_string(to_jid_str)
    
    if to_jid and to_jid.domain == self.muc_domain:
      ET.SubElement(query_disco, "identity", {"category": "conference", "type": "text", "name": f"Chatrooms on {self.muc_domain}"})
      ET.SubElement(query_disco, "feature", {"var": NS['muc']})
    elif to_jid_str == self.upload_domain:
      ET.SubElement(query_disco, "identity", {"category": "store", "type": "file", "name": "HTTP File Upload"})
      ET.SubElement(query_disco, "feature", {"var": NS['upload']})
      form = ET.SubElement(query_disco, f"{{{NS['data']}}}x", {"type": "result"})
      field_form_type = ET.SubElement(form, "field", {"var": "FORM_TYPE", "type": "hidden"})
      ET.SubElement(field_form_type, "value").text = "urn:xmpp:http:upload:0"
      field_max_size = ET.SubElement(form, "field", {"var": "max-file-size"})
      ET.SubElement(field_max_size, "value").text = str(self.config['upload_limit_mb'] * 1024 * 1024)
    elif to_jid_str == proto.session_domain:
      ET.SubElement(query_disco, "identity", {"category": "server", "type": "im", "name": self.config['server_name']})
      for feature in [NS['disco_info'], NS['disco_items'], NS['roster'], NS['ping'], NS['upload'], NS['session'], NS['compress'], NS['vcard'], NS['version'], NS['time'], NS['last'], NS['receipts'], NS['carbons'], NS['mam_2'], NS['muc'], NS['sm'], NS['register'], NS['chatstates']]:
        ET.SubElement(query_disco, "feature", {"var": feature})
    await proto.send_xml(result_iq)

  async def handle_disco_items(self, proto: XMPPProtocol, elem: ET.Element):
    result_iq = self.create_iq_result(proto, elem); query_disco = ET.SubElement(result_iq, f"{{{NS['disco_items']}}}query")
    to_jid_str = elem.get('to', proto.session_domain)
    if to_jid_str == proto.session_domain:
      ET.SubElement(query_disco, "item", {"jid": self.muc_domain, "name": "Chatrooms"})
      ET.SubElement(query_disco, "item", {"jid": self.upload_domain, "name": "File Upload"})
    elif to_jid_str == self.muc_domain:
      for room_name in self.muc.rooms.keys(): ET.SubElement(query_disco, "item", {"jid": room_name, "name": room_name.split('@')[0]})
    await proto.send_xml(result_iq)

  async def handle_upload_request(self, proto: XMPPProtocol, elem: ET.Element):
    query = elem.find(f".//{{{NS['upload']}}}request")
    if query is None: return await proto.send_xml(self.create_iq_error(proto, elem, 'modify', 'bad-request'))
    filename = query.get('filename')
    size_str = query.get('size')
    content_type = query.get('content-type', '')
    if not filename or not size_str: return await proto.send_xml(self.create_iq_error(proto, elem, 'modify', 'bad-request'))
    try:
      file_size = int(size_str)
    except (ValueError, TypeError):
      return await proto.send_xml(self.create_iq_error(proto, elem, 'modify', 'bad-request'))
    is_valid, error_msg = await self.validate_file_upload(filename, content_type, file_size, str(proto.jid))
    if not is_valid:
      return await proto.send_xml(self.create_iq_error(
        proto, elem, 'modify', 'not-acceptable',
        text=error_msg,
        app_error_name='file-too-large' if 'large' in error_msg.lower() else 'not-acceptable',
        app_error_ns=NS['upload']
      ))
    file_uuid = str(uuid.uuid4())
    slot_expiry = datetime.now(timezone.utc) + timedelta(seconds=300)
    self.upload_slots[file_uuid] = (str(proto.jid), slot_expiry)
    http_host = proto.session_domain if proto.session_domain != self.config['domain'] else self.config['host']
    put_url = f"https://{http_host}:{self.config['http_port']}/upload/{file_uuid}/{filename}"
    get_url = f"https://{http_host}:{self.config['http_port']}/upload/{file_uuid}/{filename}"
    result_iq = self.create_iq_result(proto, elem, from_jid_str=self.upload_domain)
    slot = ET.SubElement(result_iq, f"{{{NS['upload']}}}slot")
    put_elem = ET.SubElement(slot, 'put', {'url': put_url})
    ET.SubElement(put_elem, 'header', {'name': 'Content-Type'}).text = content_type or 'application/octet-stream'
    ET.SubElement(slot, 'get', {'url': get_url})
    await proto.send_xml(result_iq)
    logger.info(f"Upload slot created for {proto.jid}: {file_uuid} ({filename}, {file_size} bytes)")

  async def handle_mam_query(self, proto: XMPPProtocol, elem: ET.Element):
    query = elem.find(f".//{{{NS['mam_2']}}}query"); queryid = query.get('queryid') if query is not None else None
    form = elem.find(f".//{{{NS['rsm']}}}set"); before_id = form.findtext('before') if form is not None else None
    max_items = int(form.findtext('max', '50')) if form is not None else 50
    with_jid = query.get('with')
    results, complete = await self.db.query_archive(proto.jid.bare(), with_jid=with_jid, before_id=before_id, max_results=max_items)
    for msg in results:
      result_message = ET.Element('message', {'to': str(proto.jid)})
      result_elem = ET.SubElement(result_message, 'result', {'xmlns': NS['mam_2'], 'id': msg.id, 'queryid': queryid})
      forwarded = ET.SubElement(result_elem, 'forwarded', {'xmlns': NS['forward']})
      ET.SubElement(forwarded, 'delay', {'xmlns': NS['delay'], 'stamp': msg.timestamp.isoformat().replace('+00:00', 'Z')})
      forwarded.append(ET.fromstring(msg.stanza)); await proto.send_xml(result_message)
    fin_message = ET.Element('fin', {'xmlns': NS['mam_2'], 'complete': str(complete).lower(), 'queryid': queryid})
    set_elem = ET.SubElement(fin_message, 'set', {'xmlns': NS['rsm']})
    ET.SubElement(set_elem, 'count').text = str(len(results))
    if results: ET.SubElement(set_elem, 'first', {'index': '0'}).text = results[0].id; ET.SubElement(set_elem, 'last').text = results[-1].id
    result_iq = self.create_iq_result(proto, elem)
    result_iq.append(fin_message)
    await proto.send_xml(result_iq)

  async def handle_register_get(self, proto: XMPPProtocol, elem: ET.Element):
    result_iq = self.create_iq_result(proto, elem); query = ET.SubElement(result_iq, f"{{{NS['register']}}}query")
    ET.SubElement(query, "username"); ET.SubElement(query, "password"); await proto.send_xml(result_iq)

  async def handle_register_set(self, proto: XMPPProtocol, elem: ET.Element):
    query = elem.find(f"{{{NS['register']}}}query")
    if query is None: return await proto.send_xml(self.create_iq_error(proto, elem, 'modify', 'bad-request'))
    username = query.findtext("username"); password = query.findtext("password")
    if username and password:
      if await self.db.create_user(username, password): await proto.send_xml(self.create_iq_result(proto, elem))
      else: await proto.send_xml(self.create_iq_error(proto, elem, 'cancel', 'conflict'))
    else: await proto.send_xml(self.create_iq_error(proto, elem, 'modify', 'bad-request'))

  async def handle_presence(self, proto: XMPPProtocol, elem: ET.Element):
    if not proto.jid or not proto.user: return
    to_jid = JID.from_string(elem.get('to'))
    if to_jid and to_jid.domain == self.muc_domain: return await self.muc.handle_presence(proto, elem)
    if elem.get('type') in ('subscribe', 'subscribed', 'unsubscribe', 'unsubscribed'):
        logger.debug("Ignoring manual subscription due to auto-roster policy.")
        return
    elem.set('from', str(proto.jid))
    if elem.get('type') != 'unavailable':
      proto.user.last_presence = ET.tostring(elem, encoding='unicode'); await self.db.update_user(proto.user)
    await self.broadcast_to_roster(proto, elem)
    if not elem.get('type'):
      all_users = await self.db.get_all_users()
      for other_user in all_users:
        if other_user.username == proto.user.username: continue
        if other_user.last_presence:
          presence_to_send = ET.fromstring(other_user.last_presence)
          presence_to_send.set('to', str(proto.jid))
          await proto.send_xml(presence_to_send)
      offline_msgs = await self.db.get_and_clear_offline_messages(proto.user.username)
      if offline_msgs:
        logger.info(f"Delivering {len(offline_msgs)} offline messages to {proto.user.username}")
        for msg in offline_msgs: msg.set('to', str(proto.jid)); await proto.send_xml(msg)

  async def handle_message(self, proto: XMPPProtocol, elem: ET.Element):
    to_jid = JID.from_string(elem.get('to'))
    if not to_jid: return
    if to_jid.domain == self.muc_domain: return await self.muc.handle_message(proto, elem)
    elem.set('from', str(proto.jid))
    is_receipt = elem.find(f".//{{{NS['receipts']}}}received") is not None
    is_chatstate = any(elem.find(f'.//{{{NS["chatstates"]}}}{state}') is not None for state in ['active', 'composing', 'paused', 'inactive', 'gone'])
    msg_type = elem.get('type', 'normal')
    delivered = await self.send_to_jid(to_jid, elem)
    if elem.find(f".//{{{NS['receipts']}}}request") is not None and delivered:
      receipt = ET.Element('message', {'to': str(proto.jid), 'from': to_jid.bare()})
      ET.SubElement(receipt, f"{{{NS['receipts']}}}received", {'xmlns': NS['receipts'], 'id': elem.get('id', '')})
      await proto.send_xml(receipt)
    if not is_receipt and proto.user.carbons_enabled:
      wrapper_elem = ET.Element('message', {'to': str(proto.jid)})
      if delivered:
        sent = ET.SubElement(wrapper_elem, 'sent', {'xmlns': NS['carbons']})
        forwarded = ET.SubElement(sent, 'forwarded', {'xmlns': NS['forward']})
        forwarded.append(elem)
      else:
        received = ET.SubElement(wrapper_elem, 'received', {'xmlns': NS['carbons']})
        forwarded = ET.SubElement(received, 'forwarded', {'xmlns': NS['forward']})
        forwarded.append(elem)
      await self.broadcast_to_user(proto.user.username, wrapper_elem, exclude_resource=proto.jid.resource)
    if not delivered and not is_receipt and not is_chatstate and msg_type in ('chat', 'normal') and elem.find('.//body') is not None:
      await self.db.add_offline_message(to_jid.username, elem)
    if msg_type in ('chat', 'normal') and elem.find('.//body') is not None:
      await self.db.add_to_archive(proto.jid.bare(), to_jid.bare(), elem)
      if to_jid.bare() != proto.jid.bare(): await self.db.add_to_archive(to_jid.bare(), proto.jid.bare(), elem)

  async def handle_sm_stanza(self, proto: XMPPProtocol, elem: ET.Element):
    local_name = elem.tag.rpartition('}')[-1]
    if local_name == 'enable':
      proto.sm_enabled = True; proto.sm_id = secrets.token_hex(16)
      await proto.send_xml(ET.Element(f"{{{NS['sm']}}}enabled", {'id': proto.sm_id}))
      logger.info(f"Stream Management enabled for {proto.jid} with id {proto.sm_id}")
    elif local_name == 'r':
      await proto.send_xml(ET.Element(f"{{{NS['sm']}}}a", {'h': str(proto.sm_server_handled_count)}))

  async def handle_disconnect(self, proto: XMPPProtocol):
    if proto.jid: await self.broadcast_unavailable_presence(proto); self.unregister_session(proto)

  async def broadcast_unavailable_presence(self, from_proto: XMPPProtocol):
    if not from_proto.jid: return
    presence = ET.Element('presence', {'from': str(from_proto.jid), 'type': 'unavailable'})
    await self.broadcast_to_roster(from_proto, presence)

  async def broadcast_to_roster(self, from_proto: XMPPProtocol, elem: ET.Element):
    if not from_proto.user: return
    for user in await self.db.get_all_users():
      if user.username != from_proto.user.username:
        contact_jid = JID(user.username, from_proto.session_domain)
        await self.send_to_jid(contact_jid, ET.fromstring(ET.tostring(elem)))

  async def broadcast_to_user(self, username: str, elem: ET.Element, exclude_resource: Optional[str] = None):
    for full_jid in self.user_sessions.get(username, set()).copy():
      session = self.sessions.get(full_jid)
      if session and session.jid.resource != exclude_resource:
        elem_copy = ET.fromstring(ET.tostring(elem)); elem_copy.set('to', str(session.jid)); await session.send_xml(elem_copy)

  async def send_to_full_jid(self, full_jid_str: str, elem: ET.Element):
    if (session := self.sessions.get(full_jid_str)): await session.send_xml(elem)
      
  async def send_to_jid(self, to_jid: JID, elem: ET.Element) -> bool:
    if not to_jid.username or to_jid.username not in self.user_sessions: return False
    delivered = False
    for full_jid_str in self.user_sessions.get(to_jid.username, set()).copy():
      session = self.sessions.get(full_jid_str)
      if not session or (to_jid.resource and session.jid.resource != to_jid.resource): continue
      await self.send_to_full_jid(full_jid_str, ET.fromstring(ET.tostring(elem))); delivered = True
    return delivered

  async def register_session(self, proto: XMPPProtocol) -> bool:
    full_jid = str(proto.jid); username = proto.user.username
    if full_jid in self.sessions:
      logger.warning(f"Resource conflict for {full_jid}. Closing old session.")
      old_proto = self.sessions.get(full_jid)
      if old_proto and old_proto is not proto and old_proto.transport:
        await old_proto.send_stream_error('conflict')
      self.unregister_session(old_proto)
    self.sessions[full_jid] = proto; self.user_sessions.setdefault(username, set()).add(full_jid)
    logger.info(f"Session registered: {full_jid}"); return False

  def unregister_session(self, proto: XMPPProtocol):
    if not proto or not proto.jid or not proto.user: return
    full_jid = str(proto.jid); username = proto.user.username
    if full_jid in self.sessions: del self.sessions[full_jid]
    if username in self.user_sessions:
      self.user_sessions[username].discard(full_jid)
      if not self.user_sessions[username]: del self.user_sessions[username]
    logger.info(f"Session unregistered: {full_jid}")

  def get_stream_header(self, session_domain: str, is_response=False) -> str:
    attrs = f'from="{session_domain}" id="{secrets.token_hex(16)}" version="1.0" xml:lang="en" xmlns="{NS["client"]}" xmlns:stream="{NS["stream"]}"'
    return f'<stream:stream {attrs}>' if is_response else f'<?xml version="1.0"?><stream:stream {attrs}>'

  def get_features_for_state(self, state: State, proto: XMPPProtocol) -> Optional[ET.Element]:
    features = ET.Element(f"{{{NS['stream']}}}features")
    if state == State.INIT:
      tls = ET.SubElement(features, f"{{{NS['tls']}}}starttls"); ET.SubElement(tls, f"{{{NS['tls']}}}required")
      if self.config['allow_in_band_registration']: ET.SubElement(features, f"{{{NS['register']}}}register", {'xmlns': NS['register']})
    elif state in (State.TLS_NEGOTIATED, State.COMPRESSED):
      if state == State.TLS_NEGOTIATED:
        compress = ET.SubElement(features, f"{{{NS['compress']}}}compression"); ET.SubElement(compress, 'method').text = 'zlib'
      mechs = ET.SubElement(features, f"{{{NS['sasl']}}}mechanisms"); ET.SubElement(mechs, f"{{{NS['sasl']}}}mechanism").text = 'PLAIN'
      if self.config['allow_in_band_registration']: ET.SubElement(features, f"{{{NS['register']}}}register", {'xmlns': NS['register']})
    elif state == State.AUTHENTICATED:
      ET.SubElement(features, f"{{{NS['sm']}}}sm", {'xmlns': NS['sm']})
      bind = ET.SubElement(features, f"{{{NS['bind']}}}bind"); ET.SubElement(bind, f"{{{NS['bind']}}}required")
      ET.SubElement(features, f"{{{NS['session']}}}session")
    else: return None
    return features
  
  def get_auth_success(self) -> ET.Element: return ET.Element(f"{{{NS['sasl']}}}success")

  def get_auth_failure(self) -> ET.Element:
    failure = ET.Element(f"{{{NS['sasl']}}}failure"); ET.SubElement(failure, f"{{{NS['sasl']}}}not-authorized"); return failure
    
  def create_iq_result(self, proto: XMPPProtocol, req_elem: ET.Element, from_jid_str: Optional[str] = None) -> ET.Element:
    attrs = {'type': 'result', 'id': req_elem.get('id')}
    to = req_elem.get('from'); _from = from_jid_str if from_jid_str is not None else req_elem.get('to', proto.session_domain)
    if to: attrs['to'] = to
    if _from: attrs['from'] = _from
    return ET.Element("iq", attrs)

  def create_iq_error(self, proto: XMPPProtocol, req_elem: ET.Element, err_type: str, stanza_error_name: str, *, text: Optional[str] = None, from_jid: Optional[str]=None, app_error_name: Optional[str]=None, app_error_ns: Optional[str]=None) -> ET.Element:
    attrs = {'type': 'error', 'id': req_elem.get('id')}
    to = req_elem.get('from'); _from = from_jid if from_jid is not None else req_elem.get('to', proto.session_domain)
    if to: attrs['to'] = to
    if _from: attrs['from'] = _from
    iq = ET.Element("iq", attrs); error = ET.SubElement(iq, 'error', {'type': err_type})
    ET.SubElement(error, stanza_error_name, {'xmlns': NS['stanzas_errors']})
    if text: ET.SubElement(error, 'text', {'xmlns': NS['stanzas_errors']}).text = text
    if app_error_name and app_error_ns: ET.SubElement(error, app_error_name, {'xmlns': app_error_ns})
    return iq

  def generate_self_signed_cert(self):
    cert_file = Path(self.config['cert_file'])
    key_file = Path(self.config['key_file'])
    if cert_file.exists() and key_file.exists(): return
    logger.info(f"Generating self-signed SSL certificate for domain '{self.config['domain']}'...")
    pk = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    subject = issuer = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, self.config['domain'])])
    san_list = [x509.DNSName(self.config['domain']), x509.DNSName(self.muc_domain), x509.DNSName(self.upload_domain), x509.DNSName('localhost')]
    try:
      host_ip = ipaddress.ip_address(self.config['host'])
      if not host_ip.is_unspecified: san_list.append(x509.IPAddress(host_ip))
    except ValueError: pass
    cert = (x509.CertificateBuilder().subject_name(subject).issuer_name(issuer).public_key(pk.public_key())
      .serial_number(x509.random_serial_number()).not_valid_before(datetime.now(timezone.utc))
      .not_valid_after(datetime.now(timezone.utc) + timedelta(days=3650))
      .add_extension(x509.SubjectAlternativeName(san_list), critical=False).sign(pk, hashes.SHA256()))
    with open(key_file, "wb") as f: f.write(pk.private_bytes(encoding=serialization.Encoding.PEM, format=serialization.PrivateFormat.PKCS8, encryption_algorithm=serialization.NoEncryption()))
    with open(cert_file, "wb") as f: f.write(cert.public_bytes(serialization.Encoding.PEM))

  async def validate_file_upload(self, filename: str, content_type: str, file_size: int, uploader_jid: str) -> Tuple[bool, str]:
    if file_size > self.config['max_file_size_mb'] * 1024 * 1024:
      return False, f"File too large. Maximum size: {self.config['max_file_size_mb']}MB"
    if self.config.get('allowed_file_types') and content_type not in self.config['allowed_file_types']:
      return False, f"File type not allowed: {content_type}"
    user_uploads = [u for u in await self.db.get_all_uploads() if u.uploader_jid == uploader_jid]
    if len(user_uploads) >= self.config['max_files_per_user']:
      return False, f"Maximum files per user exceeded: {self.config['max_files_per_user']}"
    dangerous_extensions = ['.exe', '.bat', '.cmd', '.scr', '.pif', '.com', '.js', '.jar']
    file_ext = Path(filename).suffix.lower()
    if file_ext in dangerous_extensions:
      return False, f"Dangerous file extension not allowed: {file_ext}"
    return True, "OK"

  async def generate_thumbnail(self, filepath: Path, upload_data: FileUpload) -> Optional[str]:
    if not self.config.get('generate_thumbnails', False) or not upload_data.content_type.startswith('image/'):
      return None
    try:
      thumbnail_dir = Path(self.config['upload_dir']) / 'thumbnails'
      thumbnail_dir.mkdir(exist_ok=True)
      thumbnail_path = thumbnail_dir / f"{upload_data.id}_thumb.jpg"
      def create_thumb():
        with Image.open(filepath) as img:
          img.thumbnail(self.config.get('thumbnail_size', (200, 200)))
          img.convert('RGB').save(thumbnail_path, 'JPEG', quality=85)
      await asyncio.get_event_loop().run_in_executor(None, create_thumb)
      return str(thumbnail_path)
    except Exception as e:
      logger.error(f"Error generating thumbnail for {upload_data.id}: {e}")
      return None

  async def handle_http_file_upload(self, request: web.Request):
    file_uuid = request.match_info['uuid']
    filename = request.match_info.get('filename', 'untitled')
    content_length = request.headers.get('Content-Length')
    if not content_length:
      return web.Response(status=400, text="Content-Length header required")
    file_size = int(content_length)
    slot_info = self.upload_slots.get(file_uuid)
    if not slot_info or datetime.now(timezone.utc) > slot_info[1]:
      return web.Response(status=403, text="Invalid or expired upload slot")
    uploader_jid_str = slot_info[0]
    content_type = request.content_type or mimetypes.guess_type(filename)[0] or 'application/octet-stream'
    is_valid, error_msg = await self.validate_file_upload(filename, content_type, file_size, uploader_jid_str)
    if not is_valid:
      return web.Response(status=400, text=error_msg)
    upload_dir = Path(self.config['upload_dir'])
    upload_dir.mkdir(parents=True, exist_ok=True)
    filepath = upload_dir / file_uuid
    try:
      bytes_received = 0
      hash_sha256 = hashlib.sha256()
      async with aiofiles.open(filepath, 'wb') as f:
        async for chunk in request.content.iter_chunked(8192):
          if bytes_received + len(chunk) > file_size:
            await aiofiles.os.remove(filepath)
            return web.Response(status=413, text="Content length mismatch")
          await f.write(chunk)
          hash_sha256.update(chunk)
          bytes_received += len(chunk)
      if bytes_received != file_size:
        await aiofiles.os.remove(filepath)
        return web.Response(status=400, text="Incomplete upload")
      
      upload_data = FileUpload(
        id=file_uuid, filename=filename, filepath=str(filepath),
        uploader_jid=uploader_jid_str, file_size=bytes_received,
        content_type=content_type, uploaded_at=datetime.now(timezone.utc),
        file_hash=hash_sha256.hexdigest(),
        expires_at=datetime.now(timezone.utc) + timedelta(hours=self.config['upload_ttl_hours'])
      )
      thumbnail_path = await self.generate_thumbnail(filepath, upload_data)
      if thumbnail_path:
        upload_data.thumbnail_path = thumbnail_path
      await self.db.save_upload(upload_data)
      self.upload_slots.pop(file_uuid, None)
      logger.info(f"File '{filename}' ({bytes_received} bytes, {upload_data.file_hash[:8]}) uploaded by {uploader_jid_str}")
      return web.Response(status=201, headers={'X-File-Hash': upload_data.file_hash, 'X-File-Size': str(bytes_received)})
    except Exception as e:
      logger.error(f"Error uploading file {file_uuid}: {e}")
      try:
        await aiofiles.os.remove(filepath)
      except:
        pass
      return web.Response(status=500, text="Upload failed")

  async def handle_http_file_download(self, request: web.Request):
    file_uuid = request.match_info['uuid']
    upload_data = await self.db.get_upload(file_uuid)
    if not upload_data:
      return web.Response(status=404, text="File not found")
    filepath = Path(upload_data.filepath)
    if not filepath.exists():
      await self.db.remove_upload(file_uuid)
      return web.Response(status=404, text="File not found on disk")
    if upload_data.expires_at and datetime.now(timezone.utc) > upload_data.expires_at:
      return web.Response(status=410, text="File has expired")
    if self.config.get('require_auth_for_download', False):
      auth_header = request.headers.get('Authorization')
      if not auth_header:
        return web.Response(status=401, text="Authentication required")
    try:
      upload_data.download_count += 1
      await self.db.save_upload(upload_data)
      client_ip = request.remote
      logger.info(f"File '{upload_data.filename}' ({file_uuid}) downloaded by {client_ip}")
      if 'thumbnail' in request.query:
        if upload_data.thumbnail_path and Path(upload_data.thumbnail_path).exists():
          return web.FileResponse(
            path=upload_data.thumbnail_path,
            headers={'Content-Type': 'image/jpeg', 'Cache-Control': 'public, max-age=86400'}
          )
        else:
          return web.Response(status=404, text="Thumbnail not available")
      headers = {
        'Content-Type': upload_data.content_type,
        'Content-Disposition': f'attachment; filename="{upload_data.filename}"',
        'X-File-Hash': upload_data.file_hash,
        'Cache-Control': 'private, max-age=3600'
      }
      return web.FileResponse(path=str(filepath), headers=headers)
    except Exception as e:
      logger.error(f"Error serving file {file_uuid}: {e}")
      return web.Response(status=500, text="Download failed")

  async def start_http_server(self) -> web.AppRunner:
    app = web.Application(); app.router.add_put('/upload/{uuid}/{filename}', self.handle_http_file_upload)
    app.router.add_get('/upload/{uuid}/{filename}', self.handle_http_file_download)
    runner = web.AppRunner(app); await runner.setup()
    site = web.TCPSite(runner, self.config['host'], self.config['http_port'], ssl_context=self.ssl_context)
    await site.start(); logger.info(f"HTTP Server listening on https://{self.config['host']}:{self.config['http_port']}")
    return runner

  async def periodic_cleanup(self):
    while True:
      await asyncio.sleep(3600); logger.info("Running periodic cleanup task...")
      now = datetime.now(timezone.utc); upload_ttl = timedelta(hours=self.config['upload_ttl_hours'])
      for upload in [up for up in await self.db.get_all_uploads() if now - up.uploaded_at > upload_ttl]:
        try:
          Path(upload.filepath).unlink(missing_ok=True); await self.db.remove_upload(upload.id)
        except Exception as e: logger.error(f"Error cleaning up upload {upload.id}: {e}")
      for slot_id in [k for k, v in self.upload_slots.items() if now > v[1]]: self.upload_slots.pop(slot_id, None)

  async def handle_iq_version(self, proto: XMPPProtocol, elem: ET.Element):
    result_iq = self.create_iq_result(proto, elem)
    query = ET.SubElement(result_iq, f"{{{NS['version']}}}query", {'xmlns': NS['version']})
    ET.SubElement(query, 'name').text = self.config['server_name']
    ET.SubElement(query, 'version').text = self.config['server_version']
    ET.SubElement(query, 'os').text = sys.platform
    await proto.send_xml(result_iq)

  async def handle_iq_time(self, proto: XMPPProtocol, elem: ET.Element):
    result_iq = self.create_iq_result(proto, elem)
    now = datetime.now(timezone.utc)
    time_elem = ET.SubElement(result_iq, f"{{{NS['time']}}}time", {'xmlns': NS['time']})
    ET.SubElement(time_elem, 'tzo').text = '+00:00'
    ET.SubElement(time_elem, 'utc').text = now.strftime('%Y-%m-%dT%H:%M:%SZ')
    await proto.send_xml(result_iq)

  async def handle_iq_last(self, proto: XMPPProtocol, elem: ET.Element):
    target_jid = JID.from_string(elem.get('to', str(proto.jid)))
    if not target_jid: return await proto.send_xml(self.create_iq_error(proto, elem, 'modify', 'bad-request', text='Invalid JID'))
    target_user = await self.db.get_user(target_jid.username)
    seconds = -1
    if target_user and target_user.last_activity:
      seconds = int((datetime.now(timezone.utc) - target_user.last_activity).total_seconds())
    result_iq = self.create_iq_result(proto, elem); result_iq.set('from', target_jid.bare())
    ET.SubElement(result_iq, f"{{{NS['last']}}}query", {'xmlns': NS['last'], 'seconds': str(seconds)})
    await proto.send_xml(result_iq)

  async def start(self):
    await self.setup(); loop = asyncio.get_running_loop()
    xmpp_server = await loop.create_server(lambda: XMPPProtocol(self), self.config['host'], self.config['xmpp_port'])
    xmpp_tls_server = None
    if self.config['xmpp_tls_port'] and self.config['xmpp_tls_port'] > 0:
        xmpp_tls_server = await loop.create_server(lambda: XMPPProtocol(self), self.config['host'], self.config['xmpp_tls_port'], ssl=self.ssl_context)
    http_runner = await self.start_http_server(); cleanup_task = asyncio.create_task(self.periodic_cleanup())
    start_time = time.time()
    
    message = [
      f"Hello! My name is {self.config['server_name']}",
      f"Started run : {datetime.fromtimestamp(start_time).strftime('%Y_%m_%d %H:%M:%S')}"
    ]
    frame(message, "BLUE")
    
    info = [f"Domain: {self.config['domain']}", f"XMPP Port (STARTTLS): {self.config['xmpp_port']}"]
    if xmpp_tls_server: info.append(f"XMPP Port (Direct TLS): {self.config['xmpp_tls_port']}")
    info.extend([f"HTTP Port: {self.config['http_port']}", f"Listening on: {self.config['host']}"])
    frame(info, "CYAN")

    try:
      await asyncio.Event().wait()
    except (asyncio.CancelledError, KeyboardInterrupt):
      logger.info("Shutdown signal received.")
    finally:
      finish_time = time.time()
      message = [
        f"My name is {self.config['server_name']} goodbye.",
        f"Started run    : {datetime.fromtimestamp(start_time).strftime('%Y_%m_%d %H:%M:%S')}",
        f"Finished run   : {datetime.fromtimestamp(finish_time).strftime('%Y_%m_%d %H:%M:%S')}",
        f"Elapsed time   : {str(timedelta(seconds=int(finish_time - start_time)))}"
      ]
      frame(message, "ORANGE")

      cleanup_task.cancel()
      try: await cleanup_task
      except asyncio.CancelledError: pass
      xmpp_server.close(); await xmpp_server.wait_closed()
      if xmpp_tls_server: xmpp_tls_server.close(); await xmpp_tls_server.wait_closed()
      await http_runner.cleanup()

cc = {
  "RESET": "\033[0m", "NOCOLOR": "\033[39m", "BLACK": "\033[30m", "DRED": "\033[31m", "DGREEN": "\033[32m",
  "ORANGE": "\033[33m", "BLUE": "\033[34m", "VIOLET": "\033[35m", "CYAN": "\033[36m", "LGRAY": "\033[37m",
  "DGRAY": "\033[90m", "RED": "\033[91m", "GREEN": "\033[92m", "YELLOW": "\033[93m", "DBLUE": "\033[94m",
  "PINK": "\033[95m", "LBLUE": "\033[96m", "WHITE": "\033[97m"
}

def frame(lines: List[str], color: str = "NOCOLOR"):
  if not isinstance(lines, list): lines = str(lines).split('\n')
  max_len = max(len(re.sub(r'\033\[\d+m', '', str(sline))) for sline in lines) if lines else 0
  frame_width = max_len + 2
  print(cc[color] + '┌' + '─' * frame_width + '┐' + cc[color])
  for sline in lines:
    stripped_len = len(re.sub(r'\033\[\d+m', '', str(sline)))
    padding = ' ' * (max_len - stripped_len)
    print(f"│ {cc['NOCOLOR']}{sline}{padding}{cc[color]} │")
  print(cc[color] + '└' + '─' * frame_width + '┘' + cc["RESET"])

def main():
  parser = argparse.ArgumentParser(description="ZigXMPP: A minimalist, single-file XMPP server.")
  parser.add_argument("--host", type=str, help=f"IP address to bind to (default: {DEFAULT_CONFIG['host']})")
  parser.add_argument("--domain", type=str, help=f"XMPP domain name (default: {DEFAULT_CONFIG['domain']})")
  parser.add_argument("--xmpp-port", type=int, help=f"Port for STARTTLS XMPP connections (default: {DEFAULT_CONFIG['xmpp_port']})")
  parser.add_argument("--xmpp-tls-port", type=int, help=f"Port for direct TLS XMPP connections (default: {DEFAULT_CONFIG['xmpp_tls_port']})")
  parser.add_argument("--http-port", type=int, help=f"Port for HTTP file transfers (default: {DEFAULT_CONFIG['http_port']})")
  parser.add_argument("--users-file", type=str, help=f"Path to users file (default: {DEFAULT_CONFIG['users_file']})")
  parser.add_argument("--data-dir", type=str, help=f"Directory for data storage (default: {DEFAULT_CONFIG['data_dir']})")
  parser.add_argument("--log-level", type=str, choices=['DEBUG', 'INFO', 'WARNING', 'ERROR'], help=f"Logging level (default: {DEFAULT_CONFIG['log_level']})")
  args = parser.parse_args()

  config = DEFAULT_CONFIG.copy()
  for key, value in vars(args).items():
    if value is not None:
      config[key] = value

  logging.basicConfig(level=config['log_level'].upper(), format='%(asctime)s - %(levelname)s - %(message)s')
  global logger
  logger = logging.getLogger(config['server_name'])
  
  users_file = Path(config['users_file'])
  if not users_file.exists():
    logger.warning(f"'{users_file}' not found. Creating a sample file.")
    with open(users_file, 'w') as f:
      f.write("# Format: username password\n")
      f.write("alice strongpassword123\n")
      f.write("bob anotherpassword456\n")

  server = ZigXMPPServer(config)
  try:
    asyncio.run(server.start())
  except (KeyboardInterrupt, asyncio.CancelledError):
    logger.info("Server stopped by user.")
  except Exception as e:
    logger.critical(f"Critical server error: {e}", exc_info=True)

if __name__ == '__main__':
  main()

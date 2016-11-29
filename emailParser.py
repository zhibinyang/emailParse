# -*- coding: utf-8 -*-
#
# emlParser is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# emlPrser is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with eml_parser.  If not, see <http://www.gnu.org/licenses/>.
#
#
# Functionality inspired by:
#   https://github.com/CybOXProject/Tools/blob/master/scripts/email_to_cybox/email_to_cybox.py
#   https://github.com/iscoming/eml_parser/blob/master/eml_parser.py
#   https://github.com/sim0nx/eml_parser
#
# Regular expressions and subject field decoding inspired by:
#   "A Really Ruby Mail Library" - https://github.com/mikel/mail (MIT)
#
#

import sys
import email
#import getopt
import re
import uuid
import datetime
import calendar
import dateutil.tz
import dateutil.parser
import base64
import hashlib
import quopri
#import time
from urlparse import urlparse

try:
  import chardet
except ImportError:
  chardet = None

try:
  from python_magic import magic
except ImportError:
  magic = None


# regex compilation
# W3C HTML5 standard recommended regex for e-mail validation
email_regex = re.compile(r'''([a-zA-Z0-9.!#$%&'*+-/=?\^_`{|}~-]+@[a-zA-Z0-9-]+(?:\.[a-zA-Z0-9-]+)*)''', re.MULTILINE)

domain_regex = re.compile(r'''(?:(?:from|by)\s+)?([a-zA-Z0-9-]+(?:\.[a-zA-Z0-9-]+)+)''', re.MULTILINE)
ipv4_regex = re.compile(r'''((?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?))''', re.MULTILINE)

b_d_regex = re.compile(r'(localhost|[a-z0-9.\-]+(?:[.][a-z]{2,4})?)')
f_d_regex = re.compile(r'from(?:\s+(localhost|[a-z0-9\-]+|[a-z0-9.\-]+[.][a-z]{2,4}))?\s+(?:\(?(localhost|[a-z0-9.\-]+[.][a-z]{2,4})?\s*\[(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})\]\)?)?')
for_d_regex = re.compile(r'for\s+<?([a-z0-9.\-]+@[a-z0-9.\-]+[.][a-z]{2,4})>?')

# note: depending on the text this regex blocks in an infinite loop !
url_regex = re.compile(r'''(?i)\b((?:(hxxps?|https?|ftps?)://|www\d{0,3}[.]|[a-z0-9.\-]+[.][a-z]{2,4}/)(?:[^\s()<>]+|\(([^\s()<>]+|(\([^\s()<>]+\)))*\))+(?:\(([^\s()<>]+|(\([^\s()<>]+\)))*\)|[^\s`!()\[\]{};:'".,<>?]))''', re.VERBOSE | re.MULTILINE)

# simple version for searching for URLs
url_regex_simple = re.compile(r'''(?i)\b((?:(hxxps?|https?|ftps?)://)[^ ]+)''', re.VERBOSE | re.MULTILINE)

# encoded string =?<encoding>?[QB]?<string>?=
re_encoded_string = re.compile(r'\=\?[^?]+\?[QB]\?[^?]+?\?\=', (re.X | re.M | re.I))

re_quoted_string = re.compile(r'''(                               # Group around entire regex to include it in matches
                                   \=\?[^?]+\?([QB])\?[^?]+?\?\=  # Quoted String with subgroup for encoding method
                                   |                              # or
                                   .+?(?=\=\?|$)                  # Plain String
                                  )''', (re.X | re.M | re.I))

re_q_value = re.compile(r'\=\?(.+)?\?[Qq]\?(.+)?\?\=')
re_b_value = re.compile(r'\=\?(.+)?\?[Bb]\?(.+)?\?\=')

################################################


class EmailParser(object):
    def __init__(self, _Debug = False):
        self.maila = {}
        self.header = {}
        self.mailObject = None
        self.isEmailDecoded = False;
        self.charset = "ascii"
        self._debug = _Debug
        if self._debug:
            print "EmailParser Constructor"

    def getRawBodyText(self, msg):
      if self._debug:
          print "Method get_raw_text\n"
      raw_body = []
    
      if not msg.is_multipart():
        # Treat text document attachments as belonging to the body of the mail.
        # Attachments with a file-extension of .htm/.html are implicitely treated
        # as text as well in order not to escape later checks (e.g. URL scan).
        if (not 'content-disposition' in msg and msg.get_content_maintype() == 'text') or\
           (msg.get_filename('').lower().endswith('.html') or msg.get_filename('').lower().endswith('.htm')):
          encoding = msg.get('content-transfer-encoding', '').lower()
    
          charset = msg.get_content_charset()
          print "charset: ", charset
          if not charset:
            raw_body_str = msg.get_payload(decode=True)
          else:
            try:
              self.charset = charset
              raw_body_str = msg.get_payload(decode=True).decode(charset, 'ignore')
            except:
              self.charset = "ascii"
              raw_body_str = msg.get_payload(decode=True).decode('ascii', 'ignore')
    
          raw_body.append((encoding, raw_body_str))
      else:
        for part in msg.get_payload():
          raw_body.extend(self.getRawBodyText(part))
    
      return raw_body
    
    
    def getFileExtension(self, filename):
      if self._debug:
          print "Method: getFileExtension\n"
      extension = ''
      dot_idx = filename.rfind('.')
    
      if dot_idx != -1:
        extension = filename[dot_idx + 1:]
    
      return extension
    
    
    def getFileHashes(self, data):
      if self._debug:
          print "Method getFileHashes\n"

      hashalgo = ['md5', 'sha1', 'sha256', 'sha384', 'sha512']
      hashes = {}
    
      for k in hashalgo:
        ha = getattr(hashlib, k)
        h = ha()
        h.update(data)
        hashes[k] = h.hexdigest()
    
      return hashes
    
    
    def traverseMultipart(self, msg, counter=0, include_attachment_data=False, fileIndex=0):
      if self._debug:
          print "Method: traverseMultipart\n"
      attachments = {}
    
      if msg.is_multipart():
        for part in msg.get_payload():
          attachments.update(self.traverseMultipart(part, counter, include_attachment_data, fileIndex))
      else:
        lower_keys = dict((k.lower(), v) for k, v in msg.items())
    
        if 'content-disposition' in lower_keys or not msg.get_content_maintype() == 'text':
          # if it's an attachment-type, pull out the filename
          # and calculate the size in bytes
          data = msg.get_payload(decode=True)
          file_size = len(data)
    
          filename = msg.get_filename('')
          if filename == '':
            filename = 'part-%03d' % (counter)
          else:
            filename = self.decodeField(filename)
    
          extension = self.getFileExtension(filename)
          hashes = self.getFileHashes(data)
              
          #file_id = str(uuid.uuid1())
          file_id = chr(fileIndex)
          attachments[file_id] = {}
          attachments[file_id]['filename'] = filename
          attachments[file_id]['size'] = file_size
          attachments[file_id]['extension'] = extension
          attachments[file_id]['hashes'] = hashes
    
          if magic:
            attachments[file_id]['mime-type'] = magic.from_buffer(data, mime=True).decode('utf-8')
          else:
            attachments[file_id]['mime-type'] = 'undetermined'
    
          if include_attachment_data:
            attachments[file_id]['raw'] = base64.b64encode(data)
    
          counter += 1
          fileIndex += 1
    
      return attachments
    
    
    def forceStringDecode(self, string):
      if self._debug:
          print "Method forceStringDecode\n"

      if string is None:
        return ''
    
      encodings = ('latin1', 'utf-8')
      text = ''
    
      for e in encodings:
        try:
          test = string.decode(e)
          text = test
          break
        except UnicodeDecodeError:
          pass
    
      if text == '':
        text = string.decode('ascii', 'ignore')
    
      return text
    
    
    def decodeField(self, field):
      if self._debug:
          print "Method: decodeField\n"
      '''Try to get the specified field using the Header module.
         If there is also an associated encoding, try to decode the
         field and return it, else return a specified default value.'''
      text = field
    
      try:
        _decoded = email.Header.decode_header(field)
        _text, charset = _decoded[0]
      except email.errors.HeaderParseError:
        _text, charset = None, None
    
      if charset:
        try:
          text = self.decodeString(_text, charset)
        except UnicodeDecodeError:
          pass
    
      try:
        text = self.decodeValue(text)
      except UnicodeDecodeError:
        text = self.decodeString(text, 'latin-1')
    
      return text
    
    
    def decodeString(self, string, encoding):
      if self._debug:
          print "Method decodeString\n"
      try:
        value = string.decode(encoding)
      except UnicodeDecodeError:
        if chardet:
          enc = chardet.detect(string)
          try:
            if not (enc['confidence'] == 1 and enc['encoding'] == 'ascii'):
              value = value.decode(enc['encoding'])
            else:
              value = value.decode('ascii', 'ignore')
          except UnicodeDecodeError:
            value = self.forceStringDecode(string)
    
      return value
    
    
    def qValueDecode(self, string):
      if self._debug:
          print "Method qValueDecode\n"
      m = re_q_value.match(string)
      if m:
        encoding, e_string = m.groups()
        d_string = quopri.decodestring(e_string).decode(encoding, 'ignore')
      else:
        d_string = e_string.decode('utf-8', 'ignore')
    
      return d_string
    
    
    def bValueDecode(self, string):
      if self._debug:
          print "Method: bValueDecode\n"
      m = re_b_value.match(string)
      if m:
        encoding, e_string = m.groups()
        d_string = base64.decodestring(e_string).decode(encoding, 'ignore')
      else:
        d_string = e_string.decode('utf-8', 'ignore')
    
      return d_string
    
    
    # Decodes a given string as Base64 or Quoted Printable, depending on what
    # type it is.
    #
    # String has to be of the format =?<encoding>?[QB]?<string>?=
    def decodeValue(self, string):
      if self._debug:
          print "Method decodeValue\n"
      # Optimization: If there's no encoded-words in the stringing, just return it
      if not re_encoded_string.search(string):
        return string
    
      # Split on white-space boundaries with capture, so we capture the white-space as well
      string_ = u''
      for line in string.replace('\r', '').split('\n'):
        line_ = u''
    
        for text in re.split(r'([ \t])', line):
          if '=?' in text:
            # Search for occurrences of quoted or plain strings
            for m in re_quoted_string.finditer(text):
              match_s, method = m.groups()
    
              if '=?' in match_s:
                if method.lower() == 'q':
                  text = self.qValueDecode(match_s)
                elif method.lower() == 'b':
                  text = self.bValueDecode(match_s)
                else:
                  raise Exception('NOTIMPLEMENTED: Unknown method "{0}"'.format(method))
    
                text = text.replace('_', ' ')
    
                if text[0] == ' ':
                  text = text[1:]
              else:
                line_ += match_s
    
          line_ += text
    
        if len(string_) > 0 and not (string_[-1] == ' ' or line_[0] == ' '):
          string_ += ' '
    
        string_ += line_
    
      return string_
    
    
    def decodeEmail(self, eml_file, include_raw_body=False, include_attachment_data=False):
      if self._debug:
          print "Method: decodeEmail\n"
      fp = open(eml_file)
      msg = email.message_from_file(fp)
      fp.close()
      self.mailObject = msg
      self.parseEmail(msg, include_raw_body, include_attachment_data)
      self.isEmailDecoded = True
    
    
    def decodeEmailS(self, eml_file, include_raw_body=False, include_attachment_data=False):
      if self._debug:
          print "Method: decodeEmail_s\n"
      msg = email.message_from_string(eml_file)
      self.mailObject = msg
      return self.parseEmail(msg, include_raw_body, include_attachment_data)
    
    
    def parseEmail(self, msg, include_raw_body=False, include_attachment_data=False):
      # parse and decode subject
      if self._debug:
          print "Method: parseEmail\n"
      subject = msg.get('subject', '')
      self.header['subject'] = self.decodeField(subject)
    
      # messageid
      self.header['message-id'] = msg.get('message-id', '')
    
      # parse and decode from
      # @TODO verify if this hack is necessary for other e-mail fields as well
      m = email_regex.search(msg.get('from', '').lower())
      if m:
        self.header['from'] = m.group(1)
      else:
        from_ = email.utils.parseaddr(msg.get('from', '').lower())
        self.header['from'] = from_[1]
    
      # parse and decode to
      to = email.utils.getaddresses(msg.get_all('to', []))
      self.header['to'] = []
      for m in to:
        if not m[1] == '':
          self.header['to'].append(m[1].lower())
    
      # parse and decode Cc
      cc = email.utils.getaddresses(msg.get_all('cc', []))
      self.header['cc'] = []
      for m in cc:
        if not m[1] == '':
          self.header['cc'].append(m[1].lower())
    
      # parse and decode Date
      # "." -> ":" replacement is for fixing bad clients (e.g. outlook express)
      msg_date = msg.get('date').replace('.', ':')
      date_ = email.utils.parsedate_tz(msg_date)
    
      if date_ and not date_[9] is None:
        ts = email.utils.mktime_tz(date_)
        date_ = datetime.datetime.utcfromtimestamp(ts)
      else:
        date_ = email.utils.parsedate(msg_date)
        if date_:
          ts = calendar.timegm(date_)
          date_ = datetime.datetime.utcfromtimestamp(ts)
        else:
          date_ = dateutil.parser.parse('1970-01-01 00:00:00 +0000')
    
      if date_.tzname() is None:
        date_ = date_.replace(tzinfo=dateutil.tz.tzutc())
    
      self.header['date'] = date_
    
      # sender ip
      self.header['x-originating-ip'] = msg.get('x-originating-ip', '').strip('[]')
    
      # mail receiver path / parse any domain, e-mail
      # @TODO parse case where domain is specified but in parantheses only an IP
      self.header['received'] = []
      self.maila['received'] = []
      self.maila['received_emails'] = []
      self.maila['received_domains'] = []
    
      for l in msg.get_all('received'):
        l = re.sub(r'(\r|\n|\s|\t)+', ' ', l.lower())
        self.header['received'].append(l)
    
        # search for domains / e-mail addresses
        for m in domain_regex.findall(l):
          checks = True
          if '.' in m:
            try:
              #test = int(re.sub(r'[.-]', '', m))
              if not ipv4_regex.match(m) or m == '127.0.0.1':
                checks = False
            except ValueError:
              pass
    
          if checks:
            self.maila['received_domains'].append(m)
    
        m = email_regex.findall(l)
        if m:
          self.maila['received_emails'] += m
    
        # ----------------------------------------------
    
        # try to parse received lines and normalize them
        try:
          f, b = l.split('by')
          b, undef = b.split('for')
        except:
          continue
    
        b_d = b_d_regex.search(b)
        f_d = f_d_regex.search(f)
        for_d = for_d_regex.search(l)
    
        if for_d:
          self.header['to'].append(for_d.group(1))
          self.header['to'] = list(set(self.header['to']))
    
        if f_d:
          if not f_d.group(2):
            f_d_2 = ''
          else:
            f_d_2 = f_d.group(2)
          if not f_d.group(3):
            f_d_3 = ''
          else:
            f_d_3 = f_d.group(3)
    
          f = '{0} ({1} [{2}])'.format(f_d.group(1), f_d_2, f_d_3)
    
          if b_d is None:
            b = ''
          else:
            b = b_d.group(1)
    
          self.maila['received'].append([f, b])
    
      self.header['received'] = tuple(self.header['received'])
      self.maila['received_emails'] = list(set(self.maila['received_emails']))
      self.maila['received_domains'] = list(set(self.maila['received_domains']))
          
      # get raw header
      raw_body = self.getRawBodyText(msg)
      if include_raw_body:
        self.maila['raw_body'] = raw_body
        #self.maila['raw_body'] = raw_body[0][1]
      else:
        self.maila['raw_body'] = []
    
      # parse any URLs found in the body
      list_observed_urls = []
    
      for body_tup in raw_body:
          encoding, body = body_tup
    
          if sys.version_info >= (3, 0) and (isinstance(body, bytes) or isinstance(body, bytearray)):
            body = body.decode('utf-8', 'ignore')
    
          for match in url_regex_simple.findall(body):
              found_url = match[0].replace('hxxp', 'http')
              found_url = urlparse(found_url).geturl()
              # let's try to be smart by stripping of noisy bogus parts
              found_url = re.split(r'''[\', ", \,, \), \}, \\]''', found_url)[0]
    
              if found_url not in list_observed_urls:
                  list_observed_urls.append(found_url)
    
      self.maila['urls'] = list_observed_urls
    
      # parse attachments
      self.maila['attachments'] = self.traverseMultipart(msg, 0, include_attachment_data)
    
      for k, v in msg.items():
        if not k.lower() in self.header:
          if len(v) >= 2 and v[0] == '<' and v[-1] == '>':
            v = v[1:-1]
    
          self.header[k.lower()] = v
    
      self.maila['header'] = self.header
    
# --------------------------------------------------------------------
# ---------------------Set of util methods ---------------------------
# --------------------------------------------------------------------
    def checkDecodeStatus(self):
        if self.isEmailDecoded == False:
            print "Decoding not done, pls call method decodeEmail first"
            sys.exit();

    def getDate(self):
        self.checkDecodeStatus()
        return self.header['date']
        
    def getObservedURL(self):
        return self.maila['urls']
        
    def getAttachment(self):
        self.checkDecodeStatus()
        return self.maila['attachments']
        
    def getReceivedEmails(self):
        self.checkDecodeStatus()
        self.maila['received_emails']
        
    def getReceivedDomains(self):
        self.checkDecodeStatus()
        return self.maila['received_domains']
        
    def getRawBody(self):
        self.checkDecodeStatus()
        return self.maila['raw_body']
        
    def getReceivedList(self):
        self.checkDecodeStatus()
        return self.header['received']
        
    def getToList(self):
        self.checkDecodeStatus()
        return self.header['to']
        
    def getCCList(self):
        self.checkDecodeStatus()
        return self.header['cc']
        
    def getFromList(self):
        self.checkDecodeStatus()
        return self.header['from']
        
    def getSubject(self):
        self.checkDecodeStatus()
        return self.header['subject']
        
    def getMessageID(self):
        self.checkDecodeStatus()
        self.header['message-id']
        
    def getSenderIP(self):
        self.checkDecodeStatus()
        return self.header['x-originating-ip']

    #---------------- Special Flagged data -----------------------------------
    def getSpecialFlagData(self, flagStr):
        return self.mailObject.get(flagStr, '')
    #---------------- Special Flagged data End --------------------------------

# --------------------------------------------------------------------
# --------------------------------------------------------------------

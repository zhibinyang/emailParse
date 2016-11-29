# -*- coding: utf-8 -*-

import sys
import re
from urlparse import urlparse
from emailParser import EmailParser
    
def main():
    msgfile = "test-email.eml"
    email = EmailParser()
    email.decodeEmail(msgfile, include_raw_body=True)
    print "Date: ", email.getDate()
    print "Sender IP: ", email.getSenderIP()
    print "Subject: ", email.getSubject()
    print "From List: ", email.getFromList()
    print "To List: ", email.getToList()
    
    attachmentList = email.getAttachment()
    if len(attachmentList):
        for key in attachmentList:
            print "Attachment: ", attachmentList[key]['filename']


if __name__ == '__main__':
    main()

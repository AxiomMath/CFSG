module

public section

namespace CFSG.Quasithin.J4Ov

structure PEntry where
  idx : Nat
  w : String
  p : Nat
  c : Nat

@[expose] def pData : List PEntry :=
  [⟨0, "tsnftebubhbtakwawritahclnexciqbghpwdoodsuerszfryrecridwzpnncEQEAWFVEYWLGEZQFSAADMNFL\
      CWQIJQYIYFAAJMMCRXFWVHMKRSBHFRCIBIKM", 11, 0⟩,
    ⟨1, "rcnafqlcnrtcpjltukrudkrnbjckfjljyjaehpusyxtuqrtzzhblcxlctuplMAQJWUCMIEEIBZWJUZNXCVUK\
      AFOMDSBHVAVENAQBVZMHCFYUCODMOUIKUJNO", 11, 333⟩,
    ⟨2, "xrjwmqxlwgaexplomtfsavcolyonqauqfnsbrtozbeavguzvbkcvsqtxszjtWGFKSFSGSYRVSOWEXJJQZIWN\
      YMRDTXNSFZRSKXETOYMWWWQIZEJMHFSZYMFS", 23, 0⟩,
    ⟨3, "qrjrwkfuztffuzpjbwpqzpdfihspbvomthhghaytfnxfsixupynuaxhuxewsZOKHQFGCMNNPSQJYSIFJNNED\
      EKAPCKBSYKGHJKXGWZVWWQPVGIBKMGMSQVAH", 11, 0⟩,
    ⟨4, "lbkjfskpcpdiiqytdsuysoqbvffadbpekcgwvixaufpcydsiskuphuegakziVHXSGHTEFXPFSVRYIIFVJOTQ\
      QUFQBVWFUVPREJQFXOHQAODDHPFBHOPEFUBI", 23, 0⟩,
    ⟨5, "dgkwmqpfkcwgejbqxhbptedqivgmeagwzdsejbstxxipewiafazpyzkgzffsHIRZHYCRIBNDDVDBAUQTNKNI\
      ETCNOMMCHEPVQKJCEDCDFPJZJLXUYTCSEPME", 11, 48⟩,
    ⟨6, "qdadcxpjrhacvfqjfjvhfflkeiknrqqhgunwqpofboreezsttihefgkvndnsGPFYBINCXEZJJBWATXSTZEKA\
      SPBFNAEZGQXPFGDSSVOFJEOIIUTTUJNNACPB", 11, 1535⟩,
    ⟨7, "bttcyhptouotjedahdiakbytaxwofkdxqazajwcfavfcaqzpdqpxbovacbbuMMCPNVITRXHFDJYVOLJIDSVE\
      BOXTSXGRZEAKKKWASMZZFVSEEDSHGYZJOOSW", 11, 1510⟩,
    ⟨8, "vsuucxdukgudwbsesijjvkdrjqqbephjdkyyqfgtsuzhizzfqrlpxjkstctkMGELQXZBKUQQSENPJVKAFCLK\
      BNJSVHJCUVCBVEDNGNUXUQMNDYXQDOOMBEMG", 23, 0⟩,
    ⟨9, "djpvxdfkqncagwgurgjubzmhmzqgbvveuyrkjwuujjgooykcedprtzadafocIBKHPADBYKGTYSUUPTSIRTPE\
      QTGSGETYJVPHZWPQZHVWNCNRYQFXCYVCFQYO", 11, 1400⟩,
    ⟨10, "etbveccckyzettmimjptabsthjptgyzdestbdiqyjrsrkxxwzzdtufsgohplPHXGQVDSRVPKZXCIZIPFZEYS\
      PGJAKNDFSOCIUDQLLCCRAYBQJXPRJZYTYBHO", 11, 0⟩,
    ⟨11, "uurfsksfkybedetrfuxiebseckdrnpcasvdctdhninxytxyfioajcoapbskgFHGEZSBKGTDRXAUIJAEWWGPI\
      CRUZJSHCETYQSVQBRAQVSVNXAGVOORQCICIE", 23, 0⟩,
    ⟨12, "clftdxqutbhsteosspkmmduzbpuadmwzfyyrrhscgopuyxqwjfdjdxivprygGIMHIEAKXVWQMZALMSMBCOJT\
      ZURPKRUJMYUXPBBYOWYZWSMWKBPUYVUUWIPF", 11, 1773⟩,
    ⟨13, "vbfhayrghgurhqikhotgxoheakyybyuqrhyymkbyyyyazionnthprshyqifsHYDOTUYRRIDDFMYZGQOARJJJ\
      IDWABHOZFXEUICVDEKNGBDVAFWNKJVJVLGKN", 11, 0⟩,
    ⟨14, "yphseebmkfazuhqziibueeiixnhifeuudcgzpdyazqpuiwartovubhkyiirgHVASEWMMCIAQEIYQIGUJVWBS\
      SUGJACPZCQCZXQHKEKFGRSJCDGERABJMEECL", 11, 0⟩,
    ⟨15, "tqqdpjbsafwbyhuixbshsdwqmmnjlcqmfxxcprkwxawduyeifaitjogfruecXIUKJRWQQVBETARORAZAPXEV\
      FPZLNFEERLYPICGZUAOIIQVETUVZBGRQCTIR", 11, 1748⟩,
    ⟨16, "zzkqtdkvggsgetejqidiqgbyqqjvcnzquiawpsbtswogtwuwtwuzxcguwzpqIAHWDVCEUYPCISUJAMMXSJGK\
      UIXFEYYXJOBDKJVICGHUUIDXNBOBLGKWAFSM", 11, 0⟩,
    ⟨17, "kqscqbzyfmmfzlljnzrtenlyniequctevirzmyvnyivzipobipctgcmjhbvkQUQWZHPXKEXTVGOGEDICFBYA\
      FQFXPEGUBOYRAADQGUWHSIIGVEISAEQEDZFY", 11, 512⟩,
    ⟨19, "hjqhnaudbeuyaxbsjlmdxoougjntpvusfuhoeirozzgxyhkucueotuvkiiziKMQHZEYGOWGMAEFKDFZHCREM\
      TRGOKRVVANHVMBPYIPZAQDQJRYSNSYISNSDQ", 11, 1730⟩,
    ⟨20, "ofjmpsvjfuooyevfndhayxjlxkpxsawzehykdbvqvamlmqirdcvtctlpfhvfESZVPISUWHFAPNENXCVWZYSZ\
      MVYPZPFFQVCBBUREKDYTTOWZFDVBESFDGBKK", 23, 0⟩,
    ⟨21, "fglmnljyemmyueryxzshfteabsnchjjnmsqrepmnorvourryjkbyvtoxyfirAVVWSNGQLBBDPBCYOJPWUFDV\
      DJWDOCCGBROSHYICKBTVQOECHFXPRWDBIZIH", 23, 0⟩,
    ⟨22, "amttlkzrfkonhejpqyiefwimyaocxxfgajwrrkoufdxmudmplkaoacmivoraGDCIEQQCRPCIVFUFXKEFJWFT\
      MHCTYVBHWWQEPRZBHDDOACZIDIFCRBAHRESR", 11, 1811⟩,
    ⟨23, "gaolpkqaxkciatxexvicpromwwoabnjeevmuxunfjudrqxtngfcczwcqpqwjKKVPHTGPQZKPFDETAYHZYRBU\
      JQGEYJVAIKAIAIEWBXQWZIGGFUQMSWIVFFZC", 11, 1705⟩,
    ⟨26, "dnlypizowokhzxifvxmopzgemanqucxuqafieveqgqfyiafjnezjusqudrofTAQZSVNUIPJFNMEPKYCFCNMK\
      VIFKMPQDNDKGCNHXZYKZGJCUFOOHLQGHUIAP", 23, 0⟩,
    ⟨28, "ifihawjtbpyhmrcujzsqbtgwtdvnckjjbnoqfkqsqohgltfoncntvezrlsfnWCMEGIBWFOVMXRLUMOHPXHCM\
      XDLHYGOTWDMDTLFRRHVVCQBVQDCQXLYDRMJT", 23, 0⟩,
    ⟨29, "rwijnlnuhusajtpzffymkzehazutumfeyaimnanxplsurbekklminnctrwybHXPRNBVFSNUASDGIDTHGIPBB\
      SQRVXAQAWQBPSMNWHADFQXKLBZZRMCHYWZWE", 11, 0⟩,
    ⟨30, "diwphkcqlqazofluygfhqyikscgtngmdymxqublynprrfxisatdspqfkuknyDJLPCJAVSPBGYTBPBBANICYV\
      TBMGHCHKJOPDCQICNRRZFOOMKVSWHPLKEWJE", 11, 1400⟩,
    ⟨31, "famnrqhqrxdwqswkhdyicvbgprkgprxrybxtcwdzjsqbdpparyryzgddheeaZSTIYYVJKPSGSTUWFHRBKSWN\
      JIGMOKJVWQSKKARCDZIOOUQJRKVYJIFCKAYX", 11, 256⟩,
    ⟨32, "icrtywukgqkrpujtzgvcxwgewqwfwfraedxftygjeaquckuaubihqrasfzwhPZNPYPSDVJAASZFAEYQFOAUW\
      DVCJCHPBZTQVQQRJNEFNDTHAYCHNEJEHNQAS", 23, 0⟩,
    ⟨33, "pqoqjieprtmrjxctxwmefjctfsicsdqtzxhdkbxkvjpxeqbvohmjrdlvkhhbPCQXTUCCZQKAOOHPEOGOVHOE\
      QLMEMEKRVCWMUPYLRQJQWBMSPHXJXKQVRKGL", 11, 0⟩,
    ⟨34, "kiqdglfmwtmrirwjlnsykjhzuqurdamsjibznfqltjtvkprlfyqmcsldthxeUHMVPFRNPFHKIEMWPJCCFCDC\
      WPUJUCLUJTFYVBJAWBDCNROOUSIAWFTOZTJQ", 11, 68⟩,
    ⟨35, "whqhanfvvugxfhwoojmqvqztjpubbzmzhtbxdxmickdesaduvdcgeqsjwxpcUGGNJTWSSJVDPZWQMFWWOOAR\
      KFZAOSJEWIWBDXCJLMJUKCQQANQFSJXDTAQQ", 11, 0⟩,
    ⟨36, "hghlaownajndvzwyaxvggwztswapyzcuxvpaasctrxvzbkbjjdomblwdsekoFNFEMRXVTHJGUTYQBXVZNVBN\
      FGQDSHZAZYWRPRFBHQRUHTHAPJZZHDSTURXS", 11, 0⟩,
    ⟨37, "hnptisstytzrgjigcrwchszsccczkxfxqzvzylcocptiupyikgpcxxqkyejqQCDUSCCGMKBKMSTUSAKIEWFU\
      ZEWFCTRDWAGDPJSBZBUQIDRZMJURAXYTZSTS", 11, 812⟩,
    ⟨38, "awjdirvcabclxuhtfjthfumjqtyihofsvpbqofzxlokghfyvpzqmbsfqghiwBQEHEUCCOZVOHHYMBARPQZIH\
      MLPGCTHCIRIRFCBRFODIMAFCJYUPVDPQIUJJ", 23, 0⟩,
    ⟨39, "icysgdrahqvsnhneytjuvsqvbztaiqchbrbaovchivicijokaxqtqdfzcrqtKCAWUVGKVQZUOIRUTWGWXRCF\
      WMAMYQTTUPEQVCXDSYQFAFZXXQSHBXXJKRSE", 11, 1412⟩,
    ⟨40, "ypjjvuaktrigujlwnacailrlnemxiubnwetixfsclmitkoyvfhyrkfthspioSRNGYPSIFNMLPJNKPKZFGHFF\
      DCYWEMESSFOHXBFMCPRQLWJATRTQDNYAWKSI", 11, 1630⟩,
    ⟨41, "lnhiclusstcapsdsnaybilgluzpuahwwekltvcowhgzxbxplrxvboqzwkosjVYMSWVHPYBSWIWDUUIBIFVTB\
      RDJRCUWQFJHLQABGDQWPLBCYSVCNFSVRFKPY", 11, 1929⟩,
    ⟨42, "howchdvagndvuwoduhwznpkzzgkynxygedoxfaehdcjpjkcqvsaoyfsezcvuUPJBGEXRQORBMXDUQUZCBNHV\
      GSSBVKQBWJZSQHKQYMSSTRFJDMEOKYZSXBTZ", 23, 0⟩,
    ⟨43, "mleoczvvtyuozqliwzustlgoysqowwwkxlwdczitegzohebnfjdejqorgrobEPPJMDUETFHRFJDWUMASKRKE\
      FEDFKWSQFKATTOFFJXJNTPIVNOGNJDNPCUIJ", 23, 0⟩,
    ⟨44, "jqajdshqvozyzfdkgoxhfeqjbiihacajfdoesryjlmzvzagesaytfvnknpvsACJMOELCJRAIVUBUSYQCVQFI\
      ZKRVCIPEAUNACZIEECYHXVWTBTODKGJRVUQR", 23, 0⟩,
    ⟨45, "tzcawzgabcykgtyjamhlzyyjwkihxajehcwiipgczydrtsaoobgmhihiilahQHUCAEIUFLIOFZXQRYWAIFZT\
      CRPADCPDAYFYBCVYJKJJDGBRQQJBDXZWODHD", 23, 0⟩,
    ⟨46, "jnquriecxfekactoviefczbjaayohiopwzmowfcouxyvxvfacwbbiigqfdmmXZQYFKAXDSDBPHWIEOWGFJDD\
      JBUZCGJCIIJIYREDSHYPOFTTAFBNLRMPLDII", 11, 0⟩,
    ⟨48, "wpfwgvcgaphircgsymsdgdnkxcckgjibxojvzqfugvdhghdiuavznjnervguRKLIHHSPOIHIYYSXBNUVFRHC\
      VWDHFYRIUXSBVSZAUSDOFXBGUFQACPVXQDHP", 23, 0⟩]

end CFSG.Quasithin.J4Ov

module

public import CFSG.Sporadic.Recognition.LyonsFinalFamilyInputs
public import CFSG.Sporadic.Recognition.LyonsFinalBInputs

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] def core107Strings : List String :=
  ["cc", "ddd", "aa", "bb", "ee", "adcddCDDCD", "bddcdCDCDD", "edcdcddCDDCDCD", "bebebebebebe",
    "abebabebabeb", "aebeabeaebeabe", "bebaebebabababababebeabe",
    "beabebaebeabebaebababababababa", "abeabeabeaeaebebeaeabaebebebab",
    "eababaebebeababababeabaebebeabeaba", "DadbdeDc", "Dedcac", "Dacdbc", "DbcDcDe", "DDcbDca",
    "DDbcDac", "bcbebcbebcbe", "DaceceDebDece", "DabdbdbdbDeaDc", "DadacDecdc", "Dececedbeacece",
    "DacDbeaebcedbdce", "Dbecebdbeaebae", "DaDcDcdbeDb", "Dbcacbdcececec", "DaDaDacbeDbda",
    "DbdbDbdeae", "Daebaeabebecdbebdce", "acecebeacecebe", "DbeaedbDbeaedb", "DaecDbDeDaecDbDe",
    "Dabdbdceacebadeadae", "Dcaedcab", "DabDeceDcDbDecDb", "DaDeaeDbdbeDc", "abcaebecbabcaebecb",
    "DaceabcdabcdabDeab", "DabDcaDbc", "Dacecadeacbebcae", "DbDbebcedabDbabdbec", "DbDceDbdbDc",
    "DaeDebDecacbebcae", "DbDecedeaebecdba", "DebDececbDece", "Dabebecebebeadebab",
    "DaDacbDbaeDbdba", "DaedcaDcdc", "DacaDedacacacadb", "DbDcDbdaeDbca", "DbDeaeDeacecaeb",
    "DaeDbceDb", "DaDcbaceceDebca", "DbacDecDe", "DcbedecaeDeaecda", "DcbaDcbaedbcbaedba",
    "DeaeDeaeDececeb", "DacaeDbceDc", "DbcbdaeDbdbe", "DbDbdeaDbDc", "DbDeaecabDecaeb",
    "DbdaceaDbdacea", "DbDbdcaDbdaedb", "DbDeaeDbeaDbdac", "DacbdbeaeDcecDbDe",
    "DbcaDcbeaceceDcec", "DbDecDbecedbeDbec", "DbDeceabDecedbDec", "DabdaedbDbDbecdc",
    "DabdaebeaeDecdca", "DbaDcbdcedeaebea", "DabdaebeaecaDada", "DabcaecDbcecebDcecb",
    "DbaeDbeDededbacbdb", "DbeaeDcabcacdedece", "DbDeabDecebDbdcec", "DaecedcDcbaecDbDe",
    "DaecdebaecdecDceaebe", "DbDcecbedeaecbaebDeb", "Dabaededbedbebaecece", "Daebeaebedebeaebea",
    "DacebaDbDebababDceba", "DcbabeDeDedbececabec", "DbaDbaDbaDbaDbaedc", "DaedbcbaceDeaDebDec",
    "DbcebcaDbdebdbae", "DbDcecbdeabdea", "DaecbdeabdeaDc", "DbcacbaceaeDeaeDc",
    "DacbeaedbDbecdba", "kk", "kckabDebcdaDababeDea", "kdeDcbkadabededeceadbaD",
    "kdbedeaekadbceacbcbcbcaDec", "kaeabebekDeacedbeabDbdc", "kdcDbacabdcDkebeaeadecedadebe",
    "kcdcDbacabdcDckbeabaeb", "kabDbcebDebababaDkaDabacebDbeDebDbdc",
    "kecdeDcecdeDckabaeceabecaeacaD", "kdedacbeacbcebedckcedabDabcbadbaDec",
    "kbDbcebeacbdbckbeadedaDeDaeb", "kdabababedbecbdbakababcebdaDbabecdac",
    "kecdeDckcdeDcekbcaecdeabaceadcd"]

@[expose] def Rcore107 : List (List (Fin 6 × Bool)) := core107Strings.map parseWord

@[expose] def eEvCore : List EEv :=
  [([-1],
     parseWord "c",
     parseWord "abDebcdaDababeDea"),
    ([-2],
     parseWord "deDcb",
     parseWord "adabededeceadbaD"),
    ([3, 1, 3, -4, -2, -4, -3, -1, -3],
     parseWord "dbedeae",
     parseWord "adbceacbcbcbcaDec"),
    ([2, 4, 1, 4, 2, 4, 1, 3, 1, 4, 3, -4, 2, 1],
     parseWord "aeabebe",
     parseWord "DeacedbeabDbdc")]

@[expose] def trEvCore : List TrEv :=
  [(((parseWord "",
        tOfInts []),
      [(parseWord "dcDbacabdcD",
        tOfInts [-2]),
       (parseWord "ebeaeadecedadebe",
        tOfInts [-3, -2, -1, -1, -2, -4, -1, -1, -4])])),
    (((parseWord "",
        tOfInts []),
      [(parseWord "cdcDbacabdcDc",
        tOfInts [-3]),
       (parseWord "beabaeb",
        tOfInts [-1, 3, -1, 3, -4, -2, -1, -1, -4])])),
    (((parseWord "",
        tOfInts []),
      [(parseWord "abDbcebDebababaD",
        tOfInts [-4, -1]),
       (parseWord "aDabacebDbeDebDbdc",
        tOfInts [-1, -1, -1, 2, -4, -2])])),
    (((parseWord "",
        tOfInts []),
      [(parseWord "ecdeDcecdeDc",
        tOfInts [1, 1]),
       (parseWord "abaeceabecaeacaD",
        tOfInts [-4, -2, -1, -4, -1, -3, -1, -4])])),
    (((parseWord "",
        tOfInts []),
      [(parseWord "dedacbeacbcebedc",
        tOfInts [1, -2, -1]),
       (parseWord "cedabDabcbadbaDec",
        tOfInts [-3, -4, -2, -3, -4])])),
    (((parseWord "",
        tOfInts []),
      [(parseWord "bDbcebeacbdbc",
        tOfInts [1, -3, -1]),
       (parseWord "beadedaDeDaeb",
        tOfInts [-1, -1, 4, 2, -3, -1, -3, -1, -4])])),
    (((parseWord "",
        tOfInts []),
      [(parseWord "dabababedbecbdba",
        tOfInts [1, 4]),
       (parseWord "ababcebdaDbabecdac",
        tOfInts [2, 4, -2, 1, 1, 1])])),
    (((parseWord "",
        tOfInts []),
      [(parseWord "ecdeDc",
        tOfInts [1]),
       (parseWord "cdeDce",
        tOfInts [-1]),
       (parseWord "bcaecdeabaceadcd",
        tOfInts [-3, -2, -4, -3, -1, -1, -4, -3, -4])]))]

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal

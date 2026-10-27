module

public import CFSG.Certificates.CosetTableCompactColumns

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open CFSG.CosetTable

@[expose] def letterOfChar (ch : Char) : Option (Fin 6 × Bool) :=
  match ch with
  | 'c' => some (0, true)
  | 'C' => some (0, false)
  | 'd' => some (1, true)
  | 'D' => some (1, false)
  | 'a' => some (2, true)
  | 'A' => some (2, false)
  | 'b' => some (3, true)
  | 'B' => some (3, false)
  | 'e' => some (4, true)
  | 'E' => some (4, false)
  | 'k' => some (5, true)
  | 'K' => some (5, false)
  | _ => none

@[expose] def parseWord (s : String) : List (Fin 6 × Bool) := s.toList.filterMap letterOfChar

@[expose] def rbStrings : List String :=
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
    "DacbeaedbDbecdba"]

@[expose] def RB : List (List (Fin 6 × Bool)) := rbStrings.map parseWord

abbrev RB5 := restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) RB

abbrev RB4 := restrictWords (subsetOf _ [2, 3, 4]) RB5

abbrev RB3 := restrictWords (subsetOf _ [1, 2]) RB4

abbrev RB2 := restrictWords (subsetOf _ [0]) RB3

@[expose] def rbSubset (R : List (List (Fin 6 × Bool))) : Bool := RB.all fun r => R.contains r

@[expose] def bCheck : Bool :=
  subsetCheckCC RB5 [2, 3, 4] 30000 22275 && subsetCheckCC RB4 [1, 2] 30000 20160 &&
    subsetCheckCC RB3 [0] 100 6 && subsetCheckCC RB2 [] 100 2

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal

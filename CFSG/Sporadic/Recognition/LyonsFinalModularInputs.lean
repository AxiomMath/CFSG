module

public import CFSG.Sporadic.Recognition.LyonsFinalBInputs
public import CFSG.CosetTable.HintedColumns

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open CFSG.CosetTable

@[expose] def modularLearnedStrings : List String :=
  ["DaDaDacbdcdcda", "DaDaDaDaDaDa", "Dacdebcbebcbeb", "DbDbDbcdbdaedb", "DbdbeaeDbdbeae",
   "DbDbDbDbDbDb", "DbDcbeaebDbecec", "DbDecaeDbececec", "DaDcDadceDb", "DaeDbdbDcDc",
   "DbDecbeaebDbcec", "DbDbDbeDbdacb", "acbceacbebcaecbc", "DaebeaeDecedbdac",
   "DbaDbaDbaDbaDbcdba", "Dbeaedeacecacece", "DaDcbebDececbca", "DaDedacacacacadb", "DDcabDcae",
   "DacbedaedeDeaDebdb", "DadacbedececaDca", "DabDecDbDabDecDb", "DabDbebadbDbDbabaDba",
   "DaDbdcdbdaDc", "DaedeceDebDecDb", "DaDaebecebeadadebe", "DbDbdeacbdea", "DaDceaedeaceDeDca",
   "DaeDbcdcdc", "DaeDbDebDbdeaec", "DacbDbDbaeDbdba", "DbDbecdbdabDcedb", "DaDecbdeaDeDc",
   "DbcdeDbcde", "DabaDcbeceadeDebcaba", "DaDbcDaDcdc", "DabdbDeaeDbeaDc", "DabdbcaDcDceaDc",
   "DaDacbDbeDbda", "DbcdaeDbcdce", "DaDcdeacecDbDabca", "DDeacbebDededbedea", "DDeadbdecb",
   "DcdacDecdb", "DaeadbabeDaeadbabe", "DaeaedbDbDbeaDc", "Dbdacaebeaebceca",
   "DaDaDeadceDebcbeb", "DabdeaDcDaeDc", "DaceDbdbDceDc", "DaDcbdecdc", "DaDeDbcbc",
   "DabcadaDcDceaDc", "DaDbDbdeaDc", "DacDebDbdeaDb", "DbaDcbeDbaceaebea", "DbcaDcDceaDbdac",
   "DabeDbdacbDbeDc", "DbacDeabdedc", "DDedadcbcb", "DaDadcDcDbc", "DacDeadbde"]

@[expose] def modularLearned : List (List (Fin 6 × Bool)) := modularLearnedStrings.map parseWord

@[expose] def modularE : List (List (Fin 6 × Bool)) :=
  ["kckabDebcdaDababeDea", "kdeDcbkadabededeceadbaD", "kdbedeaekadbceacbcbcbcaDec",
   "kaeabebekDeacedbeabDbdc"].map parseWord

@[expose] def modularD1 : List (List (Fin 6 × Bool)) :=
  ["kbkekbkebebe", "kbkbebkbkbeb", "kbkdeDcbckbkabacacecacabaeae",
   "kbkbabaeakbkebeabaeabebe"].map parseWord

@[expose] def modularD2 : List (List (Fin 6 × Bool)) :=
  ["kdkebcacbekDkbabaDbcebabaDebD", "kdkDceacaecdkDkcaDcDbedabDbDbe",
   "kdkabdbecabakDkbaeDcbcaebacaeb", "kdkabDeDeaebckDkebcdecbceadceab"].map parseWord

@[expose] def modularD3 : List (List (Fin 6 × Bool)) :=
  ["kDbkcbaDbecebdabckbdkedbabaedaDeababDe", "kDbkcbaDbedeDcbebdabckbdkaDebaceaDeDceabe",
   "kDbkcbaDbeadbDaebdabckbdkdeacbacbacebadaea"].map parseWord

@[expose] def modularD : List (List (Fin 6 × Bool)) := modularD1 ++ modularD2 ++ modularD3

@[expose] def modularR (Rc RD : List (List (Fin 6 × Bool))) : List (List (Fin 6 × Bool)) :=
  Rc ++ modularLearned ++ RD

@[expose] def modularHints : SHints 6 where
  blocks := [
    { path := parseWord "k", rels := modularE, lim := 6,
      scan := List.range 94 },
    { path := parseWord "kbk", rels := modularD1, lim := 6,
      scan := List.range 94 },
    { path := parseWord "kdk", rels := modularD2, lim := 6,
      scan := List.range 94 },
    { path := parseWord "kDbkcbaDbe", rels := modularD3, lim := 6,
      scan := List.range 19 ++ [21, 22, 24, 25, 27, 29, 30, 32, 33, 34, 35, 36, 37, 40, 41, 42, 43,
        44, 48, 49, 55, 57, 59, 60, 61, 62, 64, 71, 73, 76, 79, 80, 86, 92] ++ List.range' 107 62 }]
  late := 6
  lateScan := List.range 94 ++ List.range' 107 62
  kCol := 6
  kScan := List.range' 94 13

@[expose] def modularCap : ℕ := 14500000

@[expose] def modularCheck (R : List (List (Fin 6 × Bool))) : Bool :=
  subsetCheckHinted R [0, 1] modularHints modularCap 9606125

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal

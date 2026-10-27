module

public import CFSG.LocalAnalysis.StandardType.TitsOvergroupCheck
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs

public section

namespace CFSG.StandardType.TitsThree

open CFSG.PSL3Four.Native CFSG.StandardType.TitsOvergroup
open CFSG.Sporadic.Schreier.Tits (titsDArr)

@[expose] def pWords : List (List Int) :=
  [[1, 2, 2, 1, 2, -1, -1, -2, 1, 2, 1, -2, 1, 2, 1, 1, -2, -1, -2, -2, -1, 2, -1, -2, -2, 1, -2,
    -2, -1, 2, 2],
   [-2, -1, 2, -1, -2, -2, 1, -2, -2, -1, 2, 2, 1, 2, -1, 2, -1, -2, -1, -2, -2, -1, -1, -2, -1, -1,
    -2, -1, -1, -2, -2, -1]]

@[expose] def nWords : List (List Int) :=
  [[1, 2, 2, 1, 2, -1, -1, -2, 1, 2, 1, -2, 1, 2, 1, 1, -2, -1, -2, -2, -1, 2, -1, -2, -2, 1, -2,
    -2, -1, 2, 2],
   [-2, -1, 2, -1, -2, -2, 1, -2, -2, -1, 2, 2, 1, 2, -1, 2, -1, -2, -1, -2, -2, -1, -1, -2, -1, -1,
    -2, -1, -1, -2, -2, -1],
   [-2, 1, -2, 1, 2, 1, -2, -1, 2, -1, 2, 2, -1, -1, -1, -2, -1, -2, -1, 2, 2, 1, 1, -2, -1, -2, 1,
    1],
   [1, 2, -1, -1, 2, 1, 1, 1, 1, -2, -1, -2, -1, -2, -2, 1, 2, 1, 2, -1, -1, -2, -2, 1, 2, 1, 2]]

@[expose] def spelled (s : String) : List Int :=
  s.toList.map fun c =>
    match c with
    | 'a' => 1
    | 'b' => 2
    | 'c' => 3
    | 'd' => 4
    | 'A' => -1
    | 'B' => -2
    | 'C' => -3
    | 'D' => -4
    | _ => 0

@[expose] def repWordStrings : List String :=
  ["a", "b", "B", "A", "aa", "ba", "ab", "bb", "BB", "AA", "Ba", "aB", "bA", "Ab", "AB", "aaa",
   "baa", "aba", "bba", "aab", "bab", "abb", "bbb", "AAA", "BBa", "aBB", "bAA", "aBa", "AAb", "Bab",
   "aaB", "abA", "bbA", "bAb", "Abb", "BBA", "ABB", "AAB", "BaB", "aBA", "ABa", "BAb", "AbA", "BAB",
   "ABA", "aaaa", "baaa", "abaa", "bbaa", "aaba", "bbba", "baab", "abab", "bbab", "aabb", "abbb",
   "bAAA", "BBaa", "aBBa", "AAAb", "BBab", "aaBB", "baBB", "abAA", "bbAA", "Baaa", "aBaa", "AAba",
   "Baba", "aaBa", "baBa", "bAAb", "Baab", "aBab", "AAbb", "Babb", "aaaB", "baaB", "abaB", "bbaB",
   "aabA", "babA", "abbA", "bbbA", "BBAA", "Abaa", "bAba", "Abba", "abAb", "bbAb", "Abab", "bAbb",
   "AABB", "BaBB", "BBaB", "ABab", "ABBa", "aBBA", "aBAA", "AABa", "BBAb", "BAAb", "bABB", "bAAB",
   "BaaB", "AAbA", "aaBA", "ABaa", "BAba", "aBAb", "aBAB", "BAbb", "BaBA", "bbAB", "AbbA", "bABA",
   "ABaB", "bAbA", "BAbA", "BABa", "BABB", "ABAA", "AABA", "AbAB", "abaaa", "bbaaa", "aabaa",
   "babaa", "abbaa", "bbbaa", "aaaba", "baaba", "ababa", "aabba", "babba", "aaaab", "bbaab",
   "aabab", "babab", "abbab", "bbbab", "baabb", "bbabb", "aabbb", "babbb", "abAAA", "aBBaa",
   "BBaba", "bAAAb", "baaBB", "abaBB", "bbaBB", "aabAA", "bbbAA", "Baaaa", "aBaaa", "AAbaa",
   "Baaba", "AAbba", "abaBa", "abAAb", "Baaab", "aBaab", "Babab", "aaBab", "baBab", "AAbbb",
   "Babbb", "AAABB", "BBaBB", "bbaaB", "aabaB", "abbaB", "BABBa", "ababA", "babbA", "abbbA",
   "aBAAb", "bAbaa", "Abbaa", "bbAba", "bAbba", "AABBa", "BaBBa", "BBaBa", "abbAb", "bbbAb",
   "BAAAb", "bAbab", "abAbb", "bbAbb", "ABBAA", "Ababb", "ABaba", "bAABB", "aBBaB", "bABab",
   "bABBa", "AAAbA", "aaBBA", "aaBAA", "baBAA", "AbAAA", "AABaa", "BaBaa", "BBAba", "bABBA",
   "bbbAB", "ABBab", "abAAB", "bbAAB", "aBaaB", "AAbaB", "AAbbA", "bABAA", "BABab", "AbABA",
   "BABaB", "ABAAB", "BaabA", "aaaBA", "baaBA", "bAbAA", "BaaBA", "BaBBA", "aabAB", "bABaa",
   "ABAba", "AABAB", "ABAAb", "ABAbb", "AAbAb", "BAbAA", "bbABa", "baBAb", "AbAAb", "ABaBB",
   "ABBaB", "aBBAB", "BABAb", "aBAbb", "AABAb", "BAbbb", "aBaBA", "babAB", "AbaaB", "AbbaB",
   "BaBaB", "BAbaB", "ABBAB", "BabAB", "abAbA", "BBaBA", "AABAA", "BAAbA", "AABaB", "BABaa",
   "bAbAb", "BABAB", "AbABB", "bbaaaa", "aaabaa", "baabaa", "babbaa", "aaaaba", "baaaba", "bbaaba",
   "bababa", "abbaba", "bbbaba", "aaabba", "abaaab", "bbbaab", "babbab", "baaabb", "bbaabb",
   "bababb", "bbbabb", "baabbb", "aabAAA", "aBBaaa", "AAAbaa", "AAAbba", "BBaaab", "baBBab",
   "bAAAbb", "abbaBB", "bbbaBB", "aBabAA", "bbabAA", "AAbbaa", "BBAABB", "abAAba", "baBaba",
   "bAAbba", "Babbba", "BBaBBa", "aabAAb", "Baaaab", "Babaab", "aaaBab", "abaBab", "abAAbb",
   "aaBabb", "bAAbbb", "baaaaB", "bbbaaB", "bbabaB", "aabbaB", "babbaB", "aBaaBB", "bbaabA",
   "BBabAA", "AbAbaB", "bbAbaa", "AABBaa", "Abbaba", "bbAbba", "ABabAA", "bAbbba", "bAABBa",
   "aBBAAb", "aBAAAb", "Ababab", "bAbbab", "AABBAb", "bAbaBA", "bbAABB", "AAbaBB", "BBaaaB",
   "AbABAA", "ABBaaB", "AbAbbb", "ABABaB", "AbAAba", "AABAAB", "bAAbAA", "BBaaBA", "AbAbbA",
   "bAbbAb", "bAABaa", "abABBA", "BBAbAA", "bbAABa", "aaBaBa", "AbbaBA", "bABAba", "BAAbab",
   "AbAbAA", "bABBAb", "BAbAAA", "BAABAb", "AAbaaB", "aaBaaB", "baBaaB", "BabbaB", "bbaBaB",
   "ABAAba", "bAbaBa", "ABaBaB", "bABaBa", "BABBab", "AbAbba", "bABAAb", "AbABaB", "ABAbAB",
   "baBaBA", "ABBAAA", "ABabaB", "AbAABB", "bABBAB", "BBAbaB", "aaBAbA", "BBAAbA", "BAABaB",
   "bbABaa", "ABaaba", "bAbabA", "bABabb", "bAAbAb", "BabbAb", "ABBaBa", "BaaBAb", "ABAABa",
   "AbAbaa", "aaBAbb", "BabaBA", "BaBaBB", "bbabAB", "aabbAB", "AbaaaB", "AbbbaB", "bAbABB",
   "abAbAB", "bAAbAB", "bAbAba", "bbAbAb", "ABABAB", "abABaB", "abABAb", "AbAbAB", "bABABB",
   "ABaaBA", "aabaaaa", "bababaa", "abbabaa", "babaaba", "ababbba", "abababb", "babbabb", "abbabbb",
   "bbbabbb", "BaaBBab", "AAAbbab", "aaBBabb", "Babbaaa", "AAbabaa", "Babaaba", "babaaBa",
   "BaaBABA", "aababaB", "aaaBBaB", "abbbabA", "bbabbbA", "abAbABA", "bbABBAA", "BBaabAB",
   "BabABAB", "BaabbaB", "BBaBBAA", "ABBaaab", "BAbabbA", "bAAbAbA", "BaBabbb", "abaBaBA",
   "bABABAA", "AAABBAb", "AbbAbAb", "AABABBA", "aBaBaaB", "ABABABa", "aaaabAB", "BBAbbAA",
   "AbbABBA", "AbabABB", "BabbAbA", "babbabba", "bbaabbab", "AABBaBBa", "AAbaabba", "AbAAbaBA",
   "baBaBaba", "bAAbaBab", "aBBabbAB", "aBaaaabA", "baBABAbaBA"]

@[expose] def repWords : List (List Int) := repWordStrings.map spelled

@[expose] def repKinds : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0,
   3, 0, 4, 0, 0, 0, 0, 3]

@[expose] def genWordStrings : List (List String) :=
  [["cdCAbADbCABCaDaba", "cdCAbADAbACADCa"],
   ["BcdAAbcbdbDbcdbcaC", "AcdBacACacacbcACBDCBdacABcBDB"], ["ACBdbAdCDAbD", "BacdbAbCbCBDa"],
   ["CBDaBACaCabdCbcABAdC", "acBdBAdacDBa"], ["acdbCAcbcAba", "BdabAABDbAbaDABaCdc"],
   ["DcABcDBdBdbcA", "cAcAbCBDcBaDBcdA"], ["CABCABdBCbAdcDADadCaBc", "aDAdaDBdbCa"],
   ["ABCAbdABCDCCaBcdAd", "AcacBDcACDadA"], ["bddBdCABCdbacBaCD", "ACdcAbcdaBCab"],
   ["aCaBcDcabcDBDcaDaCBAd", "CddbAcdbdbaBCB"],
   ["aDcbdbCacAcbDbcBcbdAdcACDBA", "DBCbCBdBaCdaDCAAbCd"],
   ["cADBdABDcacDbABAdBddadccdBA", "DCBcbacAbcbaabCadcADA"],
   ["cdADBAbdCabdcBdbcA", "cdAcbaCBCBcbaDBDaCD"],
   ["dbAcbadBDCBBDAdADbCbaCABDC", "BCaBCbadCBcDAdADb"], ["aCaCBaDaDBCdABcdC", "bABAbcBADAcBcbCDCa"],
   ["DacbCAbcaCaCAdBcaCb", "bCDABADBCACBacBCAd"], ["ACABaDABadaDABCBCAdcB", "CbdBBCDaBDC"],
   ["BDaBdCAbABDbc", "AdbaCdADcDBDCBAAdcb"], ["aDBCAbDABcACaDBdBcBaCAbaCAb", "dbABaaDADaDCAbaCAb"],
   ["ADCAbACABDcaCDcBaDADaD", "acaCdbdbaBACDBBdAbc"], ["ACaBBcbcdBaDcdaDCacd", "bDaBcACDCbACBdCBA"],
   ["cdaBDCBcaDab", "DbCdAbaDDBAcAbaCa"], ["CdBCdBacbacABCbcD", "ACaDCbdacdaba"],
   ["bCdCadADcACADaCAdcADc", "DCACbADcBcadACdabaCbAcdBdAC"],
   ["cbABCDaDbdbabdacbADA", "dbadcadcaBDbdbCd"],
   ["bDCBCBCadbCacbadadbCDBDb", "CbaaCbadbcdCBdBDaBc"],
   ["AbDCDcADacbdBadcba", "AbdBcBcBACbCacBDAb"], ["DCacBACdCACABDbaC", "bAdCBdabACBdC"],
   ["cABcBdBabcbcACA", "bCACAbacDacA"], ["acaDACDABADCbbcBadcbcb", "aDBcADAbCbdba"],
   ["AbDbABdACdcBa", "AcBAcAbACbDbDcaCdAba"], ["AdADADaBDcdaBacacBaca", "DAbCABCAddbAdadaDa"],
   ["dbCbcBCABDACa", "cdcBCdBDAba"], ["CACdadBadBCdBDaCd", "CbACaDcabDab"],
   ["cdCacdCaabCBdadaCacD", "ACbDBaCBAcDAcBcacbcBAcDCAcDC"],
   ["AdaDcdacACAbabCdadCaD", "CDAcAcAcdadAcbABcdBC"], ["CdcABDBABcDac", "bDABCBcB"],
   ["BCaCbCDbcbaCACbdCbD", "ABDcdaDcbdAdbadADCDB"],
   ["ABaDBcdBCdbADbABcbbDBADBcdBAD", "caCABdbDAdAC"],
   ["abcBDBDaDAbDBAcaCBAcDa", "CbCDBAcAbADbAdabdBa"],
   ["AbDBCDADAdadCbDaBCCBdbadAd", "cbABCaBAABcdB"],
   ["AbadbabCbABaDADcabDBda", "ADaCDadACAcbcbaCACD"],
   ["aDBaCdACDABdaDcaDAB", "BAbccbabdABcaDcaDAB"],
   ["bAcbdbDbabDCdADbCdACaCAD", "bacAdCbDDAcBcABdbAca"],
   ["dbDCAcabDbDCBcAba", "bAdcDAcbDaDCadbDCA"], ["cacdcABcaBcaadcDa", "adcDbCaDABCbbcAba"],
   ["BdBACaCbDCBAbCBAbcDA", "ACACdcAdCabADCacDBcAcabDb"],
   ["bcdbaBcadbcDABAdCbACdbadBdcA", "aBDcDaDcBdacbdb"],
   ["BacBcAdcbcbacAdAACDABaCBa", "ACaDbCbCACacaaDaCACDABaCBa"],
   ["aCbDCAdAcAc", "bCAdbcdbcAdABCadc"], ["DBacaBabcabAdadAbacd", "bdCBAACBcaCBADBDCADCAbACAbd"],
   ["DBDbcBcDABcDac", "dBdABdCbdBCdC"], [], ["AbdacBaDbacacACAADadaDc", "bdAcaCDCaBcdCbADadaDc"],
   ["CDBcbCdBDABa", "CAcbcAdbDCADAdBCADbA"],
   ["BcADCDCbadABdbCBcbAB", "CdaBaadCaDABcbdabcdaBdcBABDBdB"],
   ["CdcAdBcaDabcDbdaCBC", "BDCBacAcbCdBadCDb"],
   ["DACAcDcbaDCADcACACacA", "bADCdADCBcadACCacBCBdBcDba"], ["CbbAdAdCaCda", "BcBDADBdaBdACb"],
   ["ADBCDBdCbabcdabaDcAbDbCDcbC", "BaCDaDadCabCadAcDACBC"],
   ["bdABdAbdBdcbAdcAdBdC", "DCAcABcaDAbCba"], ["DbDadADBcdBCBcbcBa", "AdABdbCbAcBAbCBCbDabAdaD"],
   ["acaaCADbDaCD", "cBCdcdCAdacaaCDBcacDbacB"], ["BCBDBABDACAD", "cAdcAcdBaDACAdcbdADABcbdc"],
   ["cdCbcdCbbADAcBcBDcbca", "ABcDCABACacdCbbaDCACbCDBd"],
   ["ACDBdadBcDcacBCdAdC", "bcbCBDaDCBCDCbaDca"],
   ["baDbabcAdAdCDacdcaDcADbdCaba", "aCbcaBcaDbACddAdccADbdCaba"],
   ["BadbDCBC", "dbDBADCbcABDBacaD"], ["BDbdABdBDccdAdcADcbCa", "acdaDDACAbCacDaCaC"],
   ["aDBDDAdCaBBACdaBcacAcabcB", "BcBCDAdbAbdabDCBDadca"],
   ["DBcDcAdAbCdcAdacBdaBDbacAB", "CADBCBDBacaCDcaCDc"],
   ["ACDBACABdACABdAcaDaCaCDbdA", "cadbcBaCDbdA"], ["aDCdcadADbAbDc", "aDaDcdaCbACBAdc"],
   ["AbCBcbDABDcbdacBDb", "ACADbaDbdabdacBDbAcBDCdBd"],
   ["ABADCCAcABCBcBcdadBcbd", "DBCbDADADABCAcaadada"],
   ["badcDadaDAbaDbdbd", "ACDabDbdCADBaCbaCAcaddacaCaCbD"],
   ["CdcbdAcaDBADcaCdaCBDcacabc", "bacBDCdADCaD"], ["ABACBcAbaabAcD", "AbcABCADbcAcBaDCABC"],
   ["dbCbadCabaCdAbcDcADA", "cAbdadBCDBcDadbDca"], ["aDaCabDBabdBACbDaCAdC", "ADAbcdADba"],
   ["BDAdCDcaDACBcADBAbCB", "cBcADCBdBADCCadCBAcB"],
   ["CAbddBdbcABaDABccDCaDcBDA", "AbDadbDBcABcBca"], ["BDBdBCCDBdabDAD", "caaDaDaD"],
   ["BAcBcadABdcDBCdAdbCa", "cbdbAcadcAbdABDadBcdaaDACbCab"],
   ["DBcADAcaCADaDbCdcb", "DBcADAcBcDABcacAACadc"], ["ABCbABcDAcaba", "cbCaBcBc"],
   ["DCABABabcBAdC", "aCadCBacacdbcbCBcbCdCAB"],
   ["CBDBdbAcbaBDbCdCdcADbdAD", "cDcBdcbcBdbcdAbAbDB"],
   ["DAcacbCabDBcaDadBAcB", "AcBCACadBcAcbabdABcDA"], ["CaBADBAAbcb", "bcbCBcaDcAdB"],
   ["AcadBacaDCAbdadBacab", "CdADAdBcDABDaBACAbDAABcABDCBdc"],
   ["DbbAdaCacdABAdB", "bDabaDCbDadcbCAcDcA"], ["cACACDBDAb", "acDCbadadcaCbCAbCaCADAD"],
   ["CdbcdbbCbaDCaBDaBD", "CdbCdBcBcab"], ["cDAcadbDCbaCddBcdcBA", "CACbaBDcaCACD"],
   ["CadbaBcBadcBa", "BdAbADabdBdbaBdaCDbAB"], ["bADabABCAcbDBDADCBca", "bcBDbcAAdabDacdbcaDbDba"],
   ["bACabACaCBcDbdCAbACba", "AbcaCbdbCDAbACa"],
   ["bdabDAbcadCDbdadcAcAcDbCba", "aDCABdbDCbdcBCbaCBaCACBadBADB"],
   ["AdAdCBdCbdAbA", "DacADbCBADadbDCaCAbDB"], ["cBaCAdCaaDacaDcba", "aDBadBCDcaDABdBACBcD"],
   ["AdCaabcBCbabCBDADaBdcA", "DbdcdACABDDADaBdcA"],
   ["DACCDCBDcACbAdaCBadAcBc", "CbCaDAbcDBCdAcabdCad"],
   ["bdacBdAcaBADcacdabCD", "bDbAbCACBCdBADcacdabCD"],
   ["dbcdABAbdabdc", "CBCbCAcDCADbdBDCacbdacbbDCab"],
   ["aBcdBBDcAcbcbAbcDabAdA", "ABcBACAcBcabbDca"],
   ["BDBCDccDABcbCaCabDaC", "abAABcaCBDcdacadbbaCabDaC"],
   ["ADAcBCBadBabcADBAbcbcADAcAbdCb", "bcabcdAdaCBdBcaCdbac"],
   ["cacBadBAbdADACadAcD", "AcbdAbdADACaCdBDbDBc"], ["aCDBdAbDADBdccbDCabA", "BCaBAcadacdCACBac"],
   ["bacBAcBcADDaDa", "AdAbcAdacdbdAcBA"], ["DABcbcAdAB", "BCADBDCbCBCaDBaCdCBA"],
   ["CBcbcbacBc", "dabCaDaCDcADaBCDcAbCdA"], ["dACDbACAdadAcBaaDc", "ACAbadBadcBdAbaC"],
   ["BDabABCadAdCAAdBaDbcbCAcd", "AdBADcBCAcbdA"], ["CadBACBdBDBCB", "BCbdadABcBdc"],
   ["DACdabCDaCAdACBcDCbA", "cdCacaDabCaBdcBADcadBcaCbCdc"],
   ["AdbDBCaCBACdcdBcDbaCbCDbCD", "bDcbdacBaabaDBDAB"], ["cbACdBAdbdBDcBCba", "CaDBAbDbcdBCaBaBc"],
   ["dcbAdabCDCab", "BcdCBcdbCACAbDbDCB"], ["aBDADADbdbDabCDbCCbc", "bDADBdBcdAABd"],
   ["bcbcdAcDADbaada", "ABcBdCACDBCBABAcbaBDAdbDC"],
   ["dBCBDadaDCbdAdbdAcabA", "CDaCbadbDaDabDBDACad"], ["AbaDCCBacbdBAAbaC", "cABacABacDbCBCbadCbD"],
   ["ABCdADaDCdACabDBDCdcaDABacBA", "daCacDcbDcdbcdbd"],
   ["adCBaBadBCAbC", "bcdCbAbCBdACDbbADAABDACb"],
   ["acDbcDcbCBaDBAdACdBd", "ABCBCAdADDbDcaDabcBadCADc"],
   ["aCDcADaBAcbCAbDccAcba", "BDBaDCBabcDbaDbacdacdBACbcA"],
   ["acAbABdaDcaBacBAbCDbd", "dcbadCBABCDcAbDcaD"], ["bDbDADadBABdBAcAC", "dBdBCAcdACBAAdbCb"],
   ["DaCDadacBACDcBAAdcD", "dcACBADCacDabdbadaBcbadaCdb"],
   ["ADAdBcabCDDBdabADBD", "CacDABcbdCaDbcaDaDbA"], ["DbdaCaDAcAcD", "ADACADAcBdCbaBD"],
   ["CbDCDBAcabD", "BADcACBABDAbA"], ["ABCdBCbdadABCdCbaBCABd", "bDadBaCbCDBDCbaBCABd"],
   ["CbCDDBcACACbCDBac", "cAcbadCabDBCCbCD"], ["BcDBCadaDCdABcDADcBD", "bCAbADBCAD"],
   ["baDacAbCDAdacdadAbCDcADadb", "ACADCADcbCDaCDCBa"],
   ["ACADaBACacDa", "cAcbCdabCDBdCAcaDAdAcDabaDBcb"], ["abcBAcdACAcA", "aDBDbcaBacdAdCbaDbaD"],
   ["ABACaDABadbabcbaBcab", "adBcbCaCdcbAcAcBabc"], ["ABCdBdAdACACdcbDCDaba", "DBDCADABacaDbCdCBC"],
   ["ABcBCDbbAdCbaBCddCDabdcBCdb", "ABcBCDbbAdCbaBCddACBcdcbd"],
   ["BcADaaCabcABdAcBACa", "AcabCaDaDadADaBcAC"], ["CdbdaBdcabCBADCdABAcB", "adBBDbCbabAcdC"],
   ["DCBBAbAdCbDCdCbdA", "AbCdbdcDAcAca"], ["caDcACBDabdabadaC", "DbdAbaDcabcbDcBcAB"],
   ["cDbaCABaCdcdCbadBa", "DcbcBADacDaadCbadBaacbaDbacb"],
   ["DaCAdAbDcbDCaBacbad", "ABcaDcACACDbAcDaDabdB"], ["caBACAbADbABd", "BacbacadacDB"],
   ["dbdCbaDaBabdBcbaCDcaabAd", "CBDDCaDABD"], ["BCdabABACbdcBdcBDCbC", "CBAcDabADBadcBDCbC"],
   ["BAcdBdcaCABACAbDbAda", "ADaBdBaCDbdACbCadCB"],
   ["BACBABAdCbADABacbdBD", "DbcDAcacDBCbACaBCDbAdB"], ["AcdaDABAdaDAb", "caDbdacBdCDbACdacBc"],
   ["BACABAdcDAcdBaBCDCa", "DcBDAdBAbdcABDbccdba"],
   ["ADAcbaDBadaDBCDBACBdABabcdc", "BAdbaBCdCbacAbDCaCaDb"],
   ["BacBaDBabcbdaDBdC", "AdaDBdCDbDCbaDacbCBa"], ["dcDaBDCABcACbdbdb", "BDBDacbdcADCBa"],
   ["aCabDbdBaCabAdbAdcABdb", "CDbACdacaCDCDcADAd"],
   ["CdbacDCacAdCBabCBab", "ABDCbacDcAbCCBabCBabAbadCacBD"],
   ["cDbdcbDBacdbCBAbda", "AbCbDABDbCDacacBADA"], ["AdabcbadbCBDADCAdadbdbCAb", "ADADACbdbcc"],
   ["CbCDcBabDbcbDCAda", "DbAbDabc"], ["DAdBacDBcbADba", "ABADABCAbADB"],
   ["BDcdBAcAdcAbadBCBCa", "dcBCaBcbdAc"], ["cbAcdABDDAbCbaBAbaC", "bDbDcaBcDADbacA"],
   ["cAbdcBDBAcdaDCBCBd", "CBdaCABcdbCDBaCBDbADBCDAbAc"], ["DabdabcdAdCA", "aCAbACAbadBDABd"],
   ["AbCBBAcdCAbcBCabACA", "daCabABcACbDAb"], ["daDcadbdacDadBAbcbDa", "AbdaCdbdbadBAbcbDDacdcacD"],
   ["bacdaCADaCaCbCaCBD", "ADcACbdbCbcB"], ["CDBcaCDCbdBcDCbDAcBcbc", "cdCbDBcbaCbCBcABcdaCaB"],
   ["caBCacdacBCDbaBaCBC", "cDADAcABCADaCbCBc"], ["dBcdbdcBDBdAACDBDACAd", "aCAbdBDBcbCbCDBDACAd"],
   ["BaDACbdADcB", "ABCDBCbDCdaBaCaCdBdCBa"], ["dBDBBCDBACDcaac", "aCDcDcaDABDac"],
   ["BdbaCBcDbdbCaCDacBDAb", "CdbcDAcBABcaCaacbA"], ["dBdcbaBCDcbcAbccbdc", "baDcaBdAdcDABCbacBd"],
   ["DbcaCAbcaDbaDBC", "ABDbDbadcBdbaDBCaDBaBcAcbCb"], ["bACaBaCdaDbCCDcBdC", "bADAcdCBcAdCCDcBdC"],
   ["badcbadacDBA", "bDacbaCaBcBAbcBCDAb"], ["DCAbacBcaCaBacBDA", "cBDACBdbdCCab"],
   ["AdBaBADbADcaDBDCa", "CDAbdCaaCAd"], ["AcBdBdCaBacBAbdCABA", "ABAdADCbdcDABacacABdA"],
   ["AcdbdCABabcAB", "acBadAbaadBCaBDDbcba"], ["dbDbbCaBcBABcBc", "CACBCAcADBDcBcBcBcabCabdCDb"],
   ["cBACAABACBCdaCBcadbDC", "CADBcbaBcAcAABdcDAcd"], ["ACBCAdBACBCdAAbDcBCdAD", "dcBACBAdBACAbC"],
   ["AbacbdcBacdbACDBDBAcAdabdAD", "DAcbABcADbdbACDBDB"],
   ["ADaCCacAcabABCAcABc", "DadabDCabACdaCBAd"], ["dbCbDCabADBcaDABdcB", "aBdccbacABCbDaCdbAcAC"],
   ["DADACadcAcDaBCabaDA", "CbAdcABcaDaCDCadbDBa"],
   ["adACadbCadAdbADADBCadAdAcDC", "dACacABaCBdAdbADA"],
   ["DadbcaDaadcBcBADDBCD", "ABcBAdBCAbacDbdACBDAd"],
   ["acbCAdaCAdBADCbdCA", "cDcbcABcDBcdabaCBacDBABDAc"],
   ["dBADabAdADAbDBcDAD", "cbdbacdcAdcDACdCAD"], ["bcdBdCbCdabAbCd", "bcdbcdCbdBDBCABcba"],
   ["BAcDACBdaDACDCAbacBCADCA", "DBAABcabCdaacadadCA"],
   ["BdAdBADBAbCdbCbadABD", "ABDbacDCbACdbaBAdab"],
   ["dCDBadcbABCDcDbcBaDb", "cbaBCAbbdCbadaCABacB"], ["ABdBDaCBaDacAbaCdaBC", "dCadadAcDAcA"],
   ["AcabDaDcaba", "DCbCDbcaBAcBadBadadbD"], ["Abcacbcdca", "BdbAcBCdAbDbbcBDABDC"],
   ["CdcaabcaCBADBCbD", "AcDAbABDCaDBCBCbcBcdb"], ["badCDBdACDbadbcAdb", "baDcADBAbdA"],
   ["bdBdBcadBDABDcADaCADBCAbcac", "AcbDaDADaCABdaCdbadbDB"],
   ["BdCBDBaDCBcbbcbDaCABAc", "CaCbACDCbDbaaBAcDCBAAbdbcDb"],
   ["aBDcdAbAdaBCAcaBCAcb", "aBaDCdbAABdABaDcAACABD"], ["dadbCbDADAd", "BabcBcaCbADcbcDcbc"],
   ["aDABDcbcdADCBCbCBCd", "ABcbCdcDabdccAbcBaDa"], ["ABDCabCdBcdabcAcA", "cABABDBdcaDcBC"],
   ["bdCAdbcdCdbca", "bcbaDaCAbDc"], ["ACbcdAcdbdbaCAcDacdadc", "bdCabADcbADccDCab"],
   ["aBadbabDADbdACbcdA", "CaBdBAcAbaCaBACbDCa"], ["BdcBcaBCABadcbaBCDa", "AdcbABCdBcacaCBDAC"],
   ["BdAcadBCBDBBDadAcAda", "dBcadbACBCBABDBCbCdbA"], ["bdaBDcbaDca", "AbDBaDBACBadcDbDa"],
   ["dcbdACbadBacDCbaCBA", "aCdACbDBdACDcadacd"], ["DAdbDbaBcaDBAdbABaC", "AbdACBDaBAdCBa"],
   ["AbDBcBabcAbdBcabad", "CDaDaDBAcADbaBDcAbADbACDcBdABC"], ["BdcbCaCAcabcBDaDbC", "aDAdBADADCAc"],
   ["AdCbaCbdbaCDcdAdACd", "acdcBcaDbcAcDaDCCd"], ["ABCbcDAdbDCBDBACBaCda", "DbDABCDCbADcBCBaBd"],
   ["AdcABabcb", "dAcbcBADcdabadACbc"], ["ACDcdBdAdbadBCac", "CbcabcdBaDCdcBDAdbcBabCABa"],
   ["dAdAdAdADaCADBDBdBaCA", "cbdABDBdbcDbadacaBdba"], ["acAbCDcbcDBcBAdCaCabad", "dbDCaDBABDAdC"],
   ["aDadaaCdBDAdAcdAdab", "aDCbdbDbCADAdA"], ["aBdbCBcDcdadcdCBDba", "CbcBDbACDabDbCbaCDb"],
   ["cBaCABCBcaDBa", "ACdBacDadcDaCbcdbdCAca"], ["abdABCBadACADaDbDCaBA", "bdBacDbDbbcbaDBA"],
   ["DBcBCabba", "dACDBACbdaDcddAdBdAbaCa"], ["bdadacBAdACDDaBdaBa", "caCDDaDcACBaDcdAbd"],
   ["adbadcbABDadBdcbcbaDC", "ADBCDbDAAbacbAdcAbCbc"],
   ["BDaDbDacaCbdBDcAdAbA", "BDaDbDacbdcBAbDAdB"], ["ABDAcBDAcaBdbdBCbCda", "BcBcDCAdCDAbacAbCDc"],
   ["AcbcBCaCdAbdaCDcdad", "DadabcdbaCbDcBcAcdBdBa"],
   ["CbdBAdcadACbCDcAbacB", "DbCBACDBaCBDBCDcAbacB"],
   ["BcAdaCdbacaBCdcACBDB", "AdbbCDBadCCdcACBDB"],
   ["CBdcAdcBcadcabdaCaCDB", "caDadBcdAbcbDbdBaCADAcAcda"],
   ["abdabCBADBDacDADbCB", "DaDaCDbaCAcBADBA"],
   ["cbDcbcBDACBcBcaDaCbDbAbcDCb", "BcAdACbCDBadCDBdacD"],
   ["DadbACDcbcabcdacDBcBabdcabdc", "dacDBcBACBCBdACDCBA"],
   ["ACDbCdBDcbaDAcACBDcdaCB", "AdabcDbabdaDaCadABCd"], ["cdbcBCbCBACDBdcDbDaD", "ABcBBcBaCDbdA"],
   ["cADcdCDaDCadCdabdab", "BcACacbdbCBAdab"], ["DCbcAdCDBdbDadacbc", "AbCADcAbdaDcabaDABDb"],
   ["AbACAbACdacdbaca", "dCDbaDCabAACAbACAbC"], ["CADBcBDbDbCdCAbdbD", "ABDacdcaDbadCbCbbcbd"],
   ["CBDABdBabaDbCbaDB", "cdbaBCacDabcadc"], ["bDBACABDABdbdBdbCDACBCacbDBD", "adcBDbDACDbacADcbc"],
   ["dABDcACCDaBadbda", "ACbbCAbaBcbcaCdbaD"], ["aDADACdabdbAdAbcA", "ABcacADcaBBdBacBc"],
   ["daBCBCBCAcadcBAdCBACABcDcBABd", "ACadbDCdacdBCCABcDcBABd"],
   ["ABacdbCbAbDA", "adcBDBAdbAdbACBDbABCddBacDbcD"], ["cbCBacBcdAcba", "DcBCBdcBaDBdacbCDaD"],
   ["AcBdcAbcBCBCAbdbCbccAbDCBcD", "CdbCaaDbDacaCBcBDBac"],
   ["ABaDcbDBBDaBCabCAcADab", "aCADDCdabaCBdABaDcbDB"],
   ["DBdBacBcACACAAdbacdba", "caBdAcACABADacdabCA"],
   ["CbAcbAcaBAcACAbccdAba", "dCAbAdADcdCAdbACBcDb"],
   ["aDBACACACbDCBAcADbD", "BaDbADaCADAbDCBAcADbDADcAcdab"],
   ["ABcdAcBABDCdBDacacB", "cddCABcAdAcbCaDCba"],
   ["dABDCAcacBAdBdabCADABDBCdCB", "BADbDabAdbcdBCabA"],
   ["CadABCbcAdBACABDa", "BdbAcBAdcaCbAcbaCD"], ["ABaDCCbCACABdacAdCBAC", "acAdCBACACaDABDADCbaD"],
   ["ACBDaDbcaCADa", "cbDBDaBcBaBCaDBDA"], ["ADbcbcDadbDCAdbDBcAca", "BdAcbacBDAcBAbdAbd"],
   ["BDbdaCdCBdBcdACDCAd", "cAcadADaDCdcaBcBAbDAB"], ["ACDadbdaCDCAba", "AcACaaBCBadAACDaCDCAC"],
   ["CAAcaDBDDBdb", "cDBDaBDabAcdacac"], ["dAbDAcdCaaCaBDAdABAdbc", "dBdbdCDDCABDAcADbacba"],
   ["DbdAbacaBADCabDaDC", "BdadCAbcadABcADBdBAba"], ["bdaCDCBaBDcAbDcbadAcA", "ABdAbaCBBadA"],
   ["ADADbadbaDbabdadbCDCA", "badCBacDaBdaDcdbAdC"], ["bAcacaDacaDbCbD", "dBcBDcbcDcAbabdCaD"],
   ["acdCbDACaDCADBacAdaDa", "aBcDbcbdAcadBcDCA"], ["cDcBdbacbdbA", "CdAdAdAdBccDBAbCbC"],
   ["dcadbaDbbaDACDBCbDa", "dBDaBDabAdacacDabD"], ["cDBcabABDCaCBCb", "bAcddBCacdc"],
   ["AcaCAbcBcbaCdCDbABc", "CbaBdcBABADadBdcACDba"], ["BdabACbCbadbcBAbCbaD", "cbCAdadacaDC"],
   ["DabdacDAbdcAbaBcdcACa", "ACdCBBaCBdaBCbCdBACDcaBadCDca"],
   ["ADcbADaBCdadAAbCDbaBDa", "aDBdcbcBdcbDacDaBADbD"], ["DcAbACdCbdc", "cacdabcAcbAdcbadabacB"],
   ["CDaDCdACBDADcbdbcADaBAcba", "AbdBadbDbaCAdADc"],
   ["BadAbADBacDbadAADAb", "dABaBcdAdCbCBadAbADa"],
   ["dCbcdCbcAbdABadcDaC", "ACdBaaDabDbDBCBcDbadbDAb"],
   ["aCadabcDCBadb", "AdbACDBCDbDccACDaDCacDBa"], ["ADaCACdcABCdbdbdA", "AbcBABCAbCdBDbCabcBCA"],
   ["dBCbDcAcdACAbdBDADab", "AdCBACACbcACB"], ["CBdaDABaDBabD", "DBAbCbACBcdCdAdBdAdB"],
   ["CAcaCABDDbcbaBDCbD", "AcbADBCBd"], ["aDaDCaBaCADAcbada", "DcacDCbcBaCDBcADABA"],
   ["DCacDCacbcBDcBDcA", "ABCABCDbaCDacaDCacDCac"],
   ["caBcBCDbABcbacaBCDcACaB", "badcdBdBcAAbcABDADa"],
   ["BCbAcBaDDaCBdCaDabcb", "ACdcDCadACaBACDBdAda"], ["BDCbdcAACbcdcABAbd", "dACdCaBAbCbCbDAdCBDb"],
   ["ADABacABAcbDDACACdACAC", "adabDACdACbadcbACdCAC"], ["acbdCDacAdCABCBCaBcbdbd", "aDDAbacBacba"],
   ["aBCbaDBc", "aBCBDBCbdAdAdBCBa"], ["caBAcBcAcAcdabdABcD", "cdbAADaCBdCACbDcbaC"],
   ["daBDAcDBcaCa", "CbcAcdcbAcADCdcaCACab"], ["CBCdAcAD", "ABdAdBAcaBAbca"],
   ["abdcbadbcBAbDaCbCdBdBadBA", "dbAddCbADCdcADcAbACdB"],
   ["dcABCadbcbcbaBcBCDBdbabCBAcdaD", "DBcbDadBcdBcBCDBdba"],
   ["cDABCadcaBCdbDCBdABadBd", "CDbDcDcaDbcBaDcbA"], ["BAdADAdcAdb", "cDCBaCdcADCdBAdCBCba"],
   ["BDBcaBAcAcDaCbDCbdCBCAcbDAcdBA", "cDBAbdcBcDBA"], ["caBdcaBdacDbcaBdbDb", "caBcBdabCBca"],
   ["BdbAbacdCBcbcDabC", "dbADcBABdBDB"], ["dAbcBAcBdcDbAcDbdBABCabAdA", "DacABdBdCaBdCDbCabCBaD"],
   ["bcBDBCAcbcDAAbaCDCbddCbdCbAC", "BdAbCBadA"], ["BAdABAdBcDcbaDcDb", "CAbcbdBCDACDcABaD"],
   ["BDbdBccDBAcDaCBdACBdABadC", "CdCABCbAcada"], ["CbabCDcbaCA", "cbcBdCaDcbaDAcAbCacA"],
   ["ABAdcaDbcaCdbDABDBad", "aCbadBCaCbdcAAcbacDC"], ["bAdbbcDBABaCbACa", "ACacdbDcaCAACacadAcd"],
   ["dCAdcabAbCBDCacAADbda", "bcaCaDbADbaCbaBcDaDBCD"],
   ["AbdCdCABdcbDCbABadbcbcab", "BACBCBDAdCabAdcaCacb"],
   ["cbCDbcdBdACDaDccBca", "ADbcDCAbCaBaCAbDadB"], ["ACbDADBCdadaDcd", "BcAcaDaBdBaCaBCdadaDcd"],
   ["ACDDAbCDCBadcbCb", "BcBCDAbcaDbdbCACbcaD"],
   ["DAdAbbcACbDaBadBabDADa", "CaBdaadadbABaCBDcbDaba"],
   ["bcDAbCabABDabDCdACaCBcdba", "cdCBACdCbDBd"], ["cACacaBcaDbCAbaBABDACa", "DADbaCBADCABaC"],
   ["aBdAcdcaCbABdcDbCdacABAdAba", "ABaDabaCaDbCDDcBadabadcDA"],
   ["DcacBADaBacABdbdaBCdAbacDBDC", "cbADBDbAcbdAcBDAcb"],
   ["BcDABdcADAdBadbDaDaCabdBc", "adaCABcDACDbc"],
   ["dBaCDbcBacDbCBcDBCACBdBacDbc", "BDacBCabADcdbCBdCbCBAbCBdcAbD"],
   ["dACdbCdaB", "DbaBCbcAACdCb"], ["BAcabcbCdABacABa", "ACabAbcbcADbAD"],
   ["abadBcaDbDADACDadbACa", "dACbDABBDCBACBaabC"],
   ["DcAdcBabdcAbaaBCBcBab", "bdcbaCBdcaBabDbaCBDbC"],
   ["bdcDACadCDaDaBdbabaBC", "BDCbcbadabCbcDCACbAcDa"],
   ["BCbcbdCbCDaBacDBcbCDDcadbDaD", "cDBdAbADBDbDabACbdC"],
   ["abdcAdBabdADaBCdaCbcBC", "baCaCdABCABcBccdca"],
   ["acDbCBcAdcBAdcbaCabAdbCA", "AbdCBCAABABAdbcDCb"], ["DabadabcDBCdb", "ADACbacACdcACBDACdcD"],
   ["ABabcADbDbaCaC", "aCaCbDbACDacAbaC"], ["ABdCADcbdBdCBcadbCAC", "caDCaBCaCdcabacBADbDCb"],
   ["dBdbDCBDaaBcDBDC", "AdcDbcBabDbDADabcADab"], ["aCDbcdbcAbCA", "bcbCadAdaCdacABCBadadAbaCDadb"],
   ["cAbAcbaDBACdba", "BacacBaDCdaDaCBadBa"], ["aCDbCDBDcbAC", "ABdBAdACBdbbdabacaD"],
   ["acBaBCdCbba", "baDbcAbacaDAdBAcdbCdcaaBcb"],
   ["CdcAcdabAbdAdcacbdcABdbdBAca", "cabDBAdADaCbbdAdcacBADCaCDc"],
   ["dbdbCdadbDAdcbcABcAcd", "BcbdABDBADAD"],
   ["aDcAbCdbDaBCbCdCAbCACDCBD", "acbDCdbaCbadAcdadAbCACDCBD"], ["CaBdCbAcbDBAbcaCa", "ABCAdCADaD"],
   ["acDcdCAdABCBACbDab", "CBcabAdcBacA"], ["DcadbcaddBacDaCD", "AbDDBaDcBdadcAdCAbAcAdAd"],
   ["AbDbAcDcADBA", "BAdCdaBaDcABcAbaCDB"], ["dAdAdAdACdCaDcBCABdCB", "CBAdAdAdcadCBCbDABa"],
   ["bDAdCaBaacBADBACabadcBdAAcAD", "bDAdCaBaBaCBDABBad"], ["caCaaBADacBD", "dacacDBaDBCDCBc"],
   ["cBAdcBcbaBDAdbCAca", "BdACdCDbaDBCCAcadCaCdACabC"],
   ["BaCbbdbadcDAbdAca", "baCBaBcAbcdBacDadb"], ["acBdaCabdBCBDCbcdCa", "BcdbDadAdCbDcAbcaDAADAb"],
   ["dbcBdbdADCbADbaBcdaDbAD", "aDCBcbcABAdbdaCaCDCbA"],
   ["BACdBdaBdcbCdad", "BAcbABcBdaDcbabcAABdCA"],
   ["dbcADadcbaCbCABDCCdbDcaBCD", "bDBCBADCBcABcbacaCd"], ["BacACBcacbacb", "AdCAcACbaBAdb"],
   ["dBcADaCDcADCBACdaBcbdacbadbD", "CaBdabadbaBC"], ["bcbcdAccBCbDBAdACAbaBDBdA", "AcBcdacAcaD"],
   ["cAbCbaDacdaCBDBBaCdCACaCBc", "cAbCbaDcdbcAcAcdc"],
   ["ABdbaCdcAAdBcDACABDAC", "cDCaDCdAADCdAbC"], ["ACACADadbCAcDBdB", "ADBADDCdABacbcaca"],
   ["CAcaacBcBAbCdcAbADAdabDaDAB", "CdcAbADABCDAdBADAd"], ["cbcaDBABcDC", "daBDACdBdbDCaCadcDaba"],
   ["acDbABaCbAdbAABCd", "AcaBcacacAc"], ["CDAdCADaCDCa", "cbadBcabCabCA"],
   ["cAdcAdAdcAdADa", "dAbdaDadAcbaCaC"], ["CBDADbABcAbdADABdBCA", "acbDbadaDbdaCbABCaDaBD"],
   ["dADaDcACbcDaDCacb", "abCDCbdBdbadbCdBAcDB"],
   ["ACBDBdadBCBdBcbAcbaCbdb", "DcbcABBCCbCbDcdACABCbD"],
   ["bCabAbAdabaCBACbcacAbCBcDcBD", "AcdAcbaBDbaDCACBcabcAbCBcDcBD"],
   ["bAcDaCbAcDBadBCdaDb", "bAcDaCbDadcAbcABCAc"], ["dabcaBAdBaCDaddBA", "dcBcBCADBc"],
   ["DAdABAdaDaCDaCadaDba", "CADabaDaddBaBdBACbcAb"],
   ["DCBCdBDAdAcAbAcAdACaD", "DAdaDAdaCaBdbAcdAcAdb"], ["CdAcbDCBdbA", "adCDcADcbDbadcDBd"],
   ["ACaCABcbABCBd", "acADacbdADbDadbAc"], ["bdCAcadbabCAcbCAcAcDBA", "DaDbaDBBDaDcAbCDaD"],
   ["bAdaaDBACAdcAcBDac", "CACAbcAbcdcBADAdABc"], ["dCACBcDABcda", "CdcABAdabDcbCdacDcaCAcABcab"],
   ["AbAcbcDaBdCba", "ACBACaDcBcDAb"], ["aDABACBABDabC", "cAdAcdABBDABcDabaBCadBACABCd"],
   ["dCBcBdABaCdbCbabaDABDb", "BabDbCdabCaCa"], ["dacdaCDBAcdbCBdBDbA", "CbCdABdBcDbDAdacdaCDB"],
   ["cAcDAdaaDCADABDacB", "cAcABcbcAbdCDa"], ["dcDaaDaBcBADbaC", "DADCABcBA"],
   ["dbDAcbcdbCAbDABaDCaDba", "ACDcaDcAbADaCABdAcdAba"],
   ["BdAcdbaDABDBcBcABaCDBdc", "CDbdcAbaCBcbcADAdcbCa"],
   ["baCBcABCBCBdABDCadba", "baCBcABCBAbaCaDcadBdaB"], ["dbddCabDcaaCaC", "cDBadAdADbcABaBAcdBaC"],
   ["cBAcADbacBCAdBaDBAb", "BaDbaBabcDbAdBabdAb"], ["BAcbcACbAcaCBDcAbdA", "AbdAAcDacBCDcdbdAdCB"],
   ["aBADCDcdaCCBaDbABdc", "CabACDcabCACdcBdAB"], ["CBCDcaCAdAdCAdbDAc", "DBcabCabbdAcaDCaca"],
   ["DcABDACadbacBAcBa", "CaBCCDABCBdAAbCA"], ["AbdCaDAdAbCBACdBabCd", "ABacbCBacbdcABAcABACAC"],
   ["AbcaaDCBacbCaCDaDCBd", "aCDaDCBdadBAcdcAAcbAD"],
   ["aCBAdbaCACBdCABA", "cdAbDABDcaCBBdABDcADDBca"], ["CbDcdBABDcbdBccacda", "cADADaCda"],
   ["cBcABDaCBdc", "aCdaDabCadCbACbdBCdAcBcabcAd"], ["BDCdaDbdBa", "bCdabABCDba"],
   ["DabAcdabacbdaccAbad", "DABaCDBcBCAcDCACdAD"], ["ABCAdCaBAbCaBDAbAcD", "bCDBDBAdCbDbdbCAbAd"],
   ["adaBAbadbdAcdabDCa", "abDbcad"], ["AcAbDcAbDbCA", "ABCabCAbdBaBCdc"],
   ["AbadCDbCD", "ADcBdCACAdCDaddAc"], ["ACABDAcdBACBacaBdadaBACbd", "CBacaBdAbdcDBACdbCbca"],
   ["CbdAABadcACaBBDBcAB", "BCBdacabADabDBDBcAB"], ["bDAbaDbbdabACAbba", "aCdadAcBdAcDDBCDcB"],
   ["CbdBdabcbabaCDbcdbc", "CBDCBdcAcdAdacDBcDcBCBCdcBa"],
   ["BcacabaCabABACa", "acAbDCbacbcDBcbcBc"], ["ACdcaBCAbACBAcbDaCbDBaDcd", "aBacdAbAdbcacAcbDa"],
   ["AdACCdaCBACAcDcaDBaD", "dbcBADaDABDBDadbDCb"],
   ["aCABdabaCdBdA", "cbadAdCACABcDaBACDabABDadbaBd"], ["ABcdbDACaDcAcbDbdBDBd", "bcDabCAdbdbCBa"],
   ["dBCBAdBAdbaBDAcbaBCB", "ADcaDABDcdcbdbddCBa"],
   ["ACAdbcBCBacAdADADACb", "bDbACBabcabcdACACdACABdaBDaca"],
   ["BADBcacDBacABCBaCACDCa", "dCACbdabdAdaDbAcDbca"],
   ["DaBCbABCBADAcDCacBADa", "CDacbaBCaDbadaDcDBdA"], ["aCaCdABdCBCBdAdBcBd", "bcBDAbDBAcADC"], [],
   ["DADbADADABacdbacaBAD", "dcAdCAdADABcACabABC"], ["BdbdbABaDbcbAcaBCAbCAb", "cbDBCBDBCA"],
   ["ADACDbcdbAdb", "ADaBCBCdAbcacadAdB"], ["bdAbcADADaDBCbADAbcdB", "ACbdadBabdCbadaCBaDB"],
   ["dBAdBBCaCdcAACdacbcbCCaca", "BaDaaBCAABdCBcDBA"],
   ["BcDbCaBdACbdcBCd", "CbCBadcbaCACbdcAcbCACBcDcbacDbCdb"],
   ["cADacADacDCaDACBaCdAd", "cADcbaDbcbD"], ["CaCDAcAbCDbCBdCD", "BAcaDCBcAbcAbCABCAbAcA"],
   ["bDcAbaCDccBcABcAbcBcDC", "BcacACaCBADbabDcAbaCDc"],
   ["bcacadABaCBabAcBabDcbABdCbcad", "cABdBcADbdBabcBdABaDC"],
   ["ACAdCbdAADAcdaCABCdc", "DADbACBacbADCaBadacda"],
   ["dCbdaDBDcbAcDadBCDcAcBDCBDaB", "bAdbcdbCaDbAdACabDABdA"],
   ["ADADBdBDCBadAdcAcAdCadAbdAb", "ABcdBaDcACADAbcAbDcACDADba"], [],
   ["cbDBaDaCABDBdbCACdadABc", "bDBaDadBCACbad"], ["DcBcdAbCACa", "AcAdbcdaBdacAbadbaBAD"],
   ["adcAcDabAbA", "acdaCdbacAcdaBCbcBcAbDaBCDac"], ["bdADCBDCAdba", "AbcbDCCdCABcAcAdA"],
   ["DcbbcABdBAcAcbDa", "CdADcbcAcAdABCdCCB"], ["CaCBaCBcabDbdacbdBcd", "BADbCCAdCbAbCaBADB"],
   ["dbdCacadAcdBcDAb", "dCaCACbcdACDaDBdACD"], [], ["abdaCBdADAbdcbdac", "DbdcadBADBACDbcADBA"],
   [], ["DAABDadAcbCBDbAACaBdacdb", "BDCADbAccbCBDbABcBcbCdBad"],
   ["aCbDABcACacbCaCbC", "aCdaDCACaCbCDbdAcbACD"], ["bDaabDCAbcA", "BaCdAcBdCbabCbdCDcAbDa"],
   ["abCabadBdAdAb", "aDCbCAcaDaDBABADbab"], []]

@[expose] def genWords : List (List (List Int)) := genWordStrings.map (·.map spelled)

@[expose] def rGenWords : List (List (List Int)) :=
  [[[-1, -1, -2, -2, 1, 1, 1, 2, 2, -1, -1, -1, 2, 2, 1, 1],
    [-1, -1, 2, 1, 2, -1, -1, -2, -2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 1, -2, -1, 2, 2, -1, -1, -1,
     -2]],
   [[-1, -1, -2, -2, 1, 1, 1, 2, 2, -1, -1, -1, 2, 2, 1, 1],
    [-2, -1, 2, -1, -2, -2, 1, -2, -2, -1, 2, 2, -1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, -1,
     -2, 1]]]

@[expose] def conjugatorWords : List (List (List Int)) :=
  [[[-1, 2, -1, -2, -1, -1, 2, -1, -2, -2, -1, -1, -2, -2, -1, 2, -1, -2, -2, 1, -2, -2, -1, 2, 2],
    [1, 2, 2, -1, 2, -1, -2, -2, 1, 1, 1, -2, -2, 1, -2, 1, 2, -1, -1, 2, 1, 2, -1, -1, -2, -2, 1,
     2, 1, 2]],
   [[-1, 2, 1, -2, -2, 1, 2, 1, 1, 2, -1, -1, -2, -1, 2, 2, 1, 1, -2, -1, -2, 1, 1, 2, 2, 1, 2, 2,
     1, 2, 2, 1, 2, 2, 1, -2, -1, 2, 2, 1, -2, 1],
    [-1, 2, 1, -2, -2, 1, 2, 1, 1, 2, -1, -1, -2, -1, 2, 2, 1, 1, -2, -1, -2, -1, -1, 2, -1, 2, 2,
     -1, 2, 1, 2, 2, -1, -1, 2, -1, -2, -1, -1, 2]]]

@[expose] def lWords (k : Nat) : List (List Int) :=
  let r := rGenWords.getD k []
  let c := conjugatorWords.getD k []
  [r.getD 0 [], r.getD 1 [], conjWord (c.getD 0 []) (r.getD 0 []),
    conjWord (c.getD 0 []) (r.getD 1 []), conjWord (c.getD 1 []) (r.getD 0 []),
    conjWord (c.getD 1 []) (r.getD 1 [])]

@[expose] def mWords (k : Nat) : List (List Int) := lWords k ++ nWords

@[expose] def piWords : List (List (List Int)) :=
  [[[-6, 5, 1], [5, -2, -3, -4, -5, -5, -4, -5, -4]], [[-2, 4, -6, -4], [3, -2, 4, -2, 4]]]

@[expose] def piBasePoints : List (List Nat) :=
  [[0], [0, 1]]

@[expose] def piRepWords : List (List Int) :=
  [[-2, -6, 3, -2], [-6, -4, 2, 2, -4]]

@[expose] def piGenWords : List (List (List Int)) :=
  [[[3, 2, 3, 2, 2, 1, 2, 1, 2, 3], [-1, -3, -3, -3, -3, -1, -3, -1, -2, -3], [-2, -3, 1, 2, -3, 1],
    [-2, -3, -3, -1, -3, 2, 1, -2, -3], [-1, 3, -2, -3, 1, -2, -3, -2, -3],
    [3, 2, 1, 3, 3, 1, 3, 3, 1]],
   [[3, 3, 1, 3, 1], [3, 1, 3, 3], [-1, -1, -2, -3, -1, -3, -3, -2, -3, -2, -3],
    [-3, -2, 3, -1, -3, -1], [1, -3, -3, -3, 1], [-3, -3, 1, -3, 1, -2, -3]]]

@[expose] def torusWords : List (List Int) :=
  [[-4, -6, -1, -6, 2], [4, -2, 1, -5, 4, 2]]

@[expose, reducible] def pairData : PairData where
  n := 1755
  gT := #[titsDArr 0, titsDArr 1]
  gOrder := 17971200
  pW := pWords
  pOrder := 27
  nW := nWords
  nOrder := 216
  fpPts := [0, 1]
  repW := repWords
  kind := repKinds
  genW := genWords
  sideW := [lWords 0, lWords 1, mWords 0, mWords 1]
  sideOrder := [5616, 5616, 11232, 11232]

@[expose, reducible] def lLocalData (k : Nat) (_ : Unit := ()) :
    Certificates.MaxD2Perm.Data where
  n := 1755
  p := 3
  gT := sideGens pairData k
  gOrder := 5616
  uW := [1]
  vW := [2]
  nW := piWords.getD k []
  nOrder := 432
  fpPts := piBasePoints.getD k []
  repW := [piRepWords.getD k []]
  genW := [piGenWords.getD k []]
  tW := torusWords.getD k []
  tm := 4
  tlam := 2
  te := 4

@[expose] def memWords : List (List (List Int)) :=
  [pWords ++ conjugatorWords.getD 0 [], pWords ++ conjugatorWords.getD 1 []]

@[expose] def titsThreeCheck (_ : Unit := ()) : Bool :=
  pairCheck pairData && checkMemW pairData memWords &&
    allBelow 2 fun k => Certificates.MaxD2Perm.check (lLocalData k ())

end CFSG.StandardType.TitsThree

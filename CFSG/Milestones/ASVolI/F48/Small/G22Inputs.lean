module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.G22Base
public import CFSG.Quasithin.Recognition.CertPermList
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertU33Phi
public import CFSG.Quasithin.Recognition.CertU33Wreath

public section

namespace CFSG.ASVolI

open CFSG.CosetTable CFSG.Quasithin

@[expose] def burnsideF48s_g22Letter (c : Char) : Fin 6 × Bool :=
  (⟨"absxyt".toList.idxOf c.toLower % 6, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def burnsideF48s_g22Word (s : String) : List (Fin 6 × Bool) :=
  s.toList.map burnsideF48s_g22Letter

@[expose] def burnsideF48s_g22InvW (w : List (Fin 6 × Bool)) : List (Fin 6 × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def burnsideF48s_g22RelP1 : List String :=
  ["ss", "tt", "yyy", "aBAb", "sAsb", "aaaa", "tAtA", "bbbb",
    "ysAyB", "YtytAb", "AYBYbb", "AstsBBat"]

@[expose] def burnsideF48s_g22RelP2 : List String :=
  ["ss", "tt", "xxx", "tBtB", "bbbb", "aaaa", "bXAx", "bsAs",
    "XsXs", "aXbxb", "aaxtXtbb", "BBtstBBs"]

@[expose] def burnsideF48s_g22CandV : List String := ["STBBXa", "TBBXTaS", "SX", "STBBx"]

@[expose] def burnsideF48s_g22Cand (j : ℕ) : List (Fin 6 × Bool) :=
  (List.replicate 6 (burnsideF48s_g22Word "bTY" ++
    burnsideF48s_g22Word (burnsideF48s_g22CandV.getD j ""))).flatten

@[expose] def burnsideF48s_g22Ws (j : ℕ) : List (List (Fin 6 × Bool)) :=
  (burnsideF48s_g22RelP1 ++ burnsideF48s_g22RelP2).map burnsideF48s_g22Word ++
    [burnsideF48s_g22Cand j]

abbrev burnsideF48s_g22WsB (j : ℕ) :=
  restrictWords (subsetOf 6 [0, 1, 2, 4, 5]) (burnsideF48s_g22Ws j)

@[expose] def burnsideF48s_g22TW : List String :=
  ["", "a", "A", "b", "B", "s", "t", "aa",
    "ab", "aB", "as", "at", "Ab", "AB", "As", "At",
    "bb", "bs", "bt", "Bs", "Bt", "st", "ts", "aab",
    "aaB", "aas", "aat", "abb", "abs", "abt", "aBs", "aBt",
    "ast", "ats", "Abb", "Abs", "Abt", "ABs", "ABt", "Ast",
    "Ats", "bbs", "bbt", "bst", "bts", "Bst", "Bts", "sts",
    "tst", "aabb", "aabs", "aabt", "aaBs", "aaBt", "aast", "aats",
    "abbs", "abbt", "abst", "abts", "aBst", "aBts", "asts", "atst"]

@[expose] def burnsideF48s_g22P1W : List String :=
  ["", "a", "A", "b", "B", "s", "t", "y",
    "Y", "aa", "ab", "aB", "as", "at", "ay", "aY",
    "Ab", "AB", "As", "At", "Ay", "AY", "bb", "bs",
    "bt", "by", "bY", "Bs", "Bt", "By", "BY", "st",
    "sy", "sY", "ts", "ty", "tY", "ya", "yA", "yb",
    "yB", "ys", "yt", "Ya", "YA", "Yb", "YB", "Ys",
    "Yt", "aab", "aaB", "aas", "aat", "aaY", "abb", "abs",
    "abt", "aby", "abY", "aBs", "aBt", "aBy", "aBY", "ast",
    "asy", "ats", "aty", "atY", "aya", "ayA", "ayb", "ayB",
    "ayt", "aYa", "aYA", "aYb", "aYB", "aYs", "aYt", "Abb",
    "Abs", "Abt", "Aby", "ABs", "ABt", "ABY", "Ast", "Asy",
    "AsY", "Ats", "Aty", "AtY", "Aya", "Ayb", "Ayt", "AYA",
    "AYb", "AYB", "AYs", "AYt", "bbs", "bbt", "bst", "bsy",
    "bsY", "bts", "bty", "btY", "bya", "bys", "byt", "Bst",
    "Bts", "Bty", "Byt", "BYA", "BYs", "BYt", "sts", "sty",
    "stY", "sya", "syt", "sYB", "sYt", "tst", "tsy", "tsY",
    "tya", "tyB", "tys", "tYa", "tYB", "tYs", "yay", "yAb",
    "ybY", "yty", "ytY", "YaB", "Yat", "Yay", "YAy", "YAY",
    "YBt", "YtY", "aabb", "aabt", "aaBs", "aaBt", "aats", "aatY",
    "aaYA", "aaYb", "aaYt", "abbs", "abbt", "abst", "absy", "abts",
    "abty", "abtY", "abyt", "aBst", "aBts", "aByt", "aBYt", "asts",
    "astY", "asyt", "atsY", "atya", "atYa", "atYs", "ayty", "aYat",
    "aYAy", "aYBt", "aYtY", "AbtY", "Abyt", "ABty", "ABYt", "AsYt",
    "Atsy", "AtyB", "AtYB", "AtYs", "bsty", "styB", "tsya", "tYaB"]

@[expose] def burnsideF48s_g22P2W : List String :=
  ["", "a", "A", "b", "B", "s", "t", "x",
    "X", "aa", "ab", "aB", "as", "at", "ax", "aX",
    "Ab", "AB", "As", "At", "Ax", "AX", "bb", "bs",
    "bt", "bx", "bX", "Bs", "Bt", "Bx", "BX", "st",
    "sx", "sX", "ts", "tx", "tX", "xa", "xA", "xt",
    "Xb", "XB", "Xt", "aab", "aaB", "aas", "aat", "aax",
    "aaX", "abb", "abs", "abt", "aBs", "aBt", "aBx", "aBX",
    "ast", "asx", "asX", "ats", "atx", "atX", "axA", "axt",
    "aXB", "aXt", "Abb", "Abs", "Abt", "Abx", "AbX", "ABs",
    "ABt", "Ast", "Asx", "AsX", "Ats", "Atx", "Axa", "Axt",
    "AXb", "bbs", "bbt", "bbx", "bbX", "bst", "bsx", "bsX",
    "bts", "btx", "btX", "bxA", "bxt", "bXB", "bXt", "Bst",
    "Bsx", "BsX", "Bts", "Btx", "BtX", "Bxa", "Bxt", "BXb",
    "BXt", "sts", "stx", "stX", "sxa", "sxA", "sxt", "sXb",
    "sXB", "sXt", "tst", "tsX", "txa", "txA", "txt", "tXb",
    "tXB", "xtx", "Xbb", "Xbt", "XBt", "Xts", "XtX", "aabb",
    "aabs", "aabt", "aaBs", "aaBt", "aast", "aasx", "aasX", "aats",
    "aaxt", "abbs", "abbt", "abst", "abts", "aBst", "aBsx", "aBsX",
    "aBts", "aBtx", "aBxt", "asts", "astx", "astX", "asxA", "asxt",
    "asXB", "asXt", "atst", "atsX", "axtx", "aXts", "Absx", "AbsX",
    "Astx", "AstX", "Asxa", "AsXb", "Axtx", "bbsx", "bbsX", "bbtX",
    "bstx", "bstX", "bsxA", "bsxt", "bsXB", "bsXt", "btsX", "bXts",
    "Bsxa", "Bsxt", "BsXb", "BtsX", "stxa", "stxA", "stxt", "stXb",
    "stXB", "sXbb", "sXbt", "sXBt", "Xbts", "XBts", "aastx", "aastX"]

@[expose] def burnsideF48s_g22GL : List (List ℕ) :=
  [[14, 20, 27, 6, 7, 5, 16, 19, 18, 1, 4, 2, 12, 15, 13, 0, 26, 17, 23, 10, 25, 8, 11, 21, 24, 9, 3, 22],
    [7, 18, 11, 3, 25, 24, 6, 9, 0, 8, 20, 22, 17, 10, 19, 4, 16, 5, 14, 1, 23, 15, 27, 13, 12, 21, 26, 2],
    [0, 10, 11, 12, 18, 16, 17, 14, 15, 13, 1, 2, 3, 9, 7, 8, 5, 6, 4, 19, 20, 21, 27, 25, 26, 23, 24, 22],
    [1, 10, 26, 24, 21, 22, 5, 20, 9, 25, 0, 3, 2, 15, 7, 23, 17, 27, 4, 19, 14, 18, 6, 13, 11, 8, 12, 16],
    [12, 13, 27, 7, 16, 8, 1, 18, 20, 26, 0, 11, 10, 6, 21, 9, 23, 25, 3, 17, 5, 24, 2, 4, 14, 19, 15, 22],
    [13, 1, 11, 6, 21, 17, 3, 23, 10, 20, 8, 2, 24, 0, 14, 15, 26, 5, 19, 18, 9, 4, 27, 7, 12, 25, 16, 22]]

@[expose] def burnsideF48s_g22GLi : List (List ℕ) :=
  [[15, 9, 11, 26, 10, 5, 3, 4, 21, 25, 19, 22, 12, 14, 0, 13, 6, 17, 8, 7, 1, 23, 27, 18, 24, 20, 16, 2],
    [8, 19, 27, 3, 15, 17, 6, 0, 9, 7, 13, 2, 24, 23, 18, 21, 16, 12, 1, 14, 10, 25, 11, 20, 5, 4, 26, 22],
    [0, 10, 11, 12, 18, 16, 17, 14, 15, 13, 1, 2, 3, 9, 7, 8, 5, 6, 4, 19, 20, 21, 27, 25, 26, 23, 24, 22],
    [10, 0, 12, 11, 18, 6, 22, 14, 25, 8, 1, 24, 26, 23, 20, 13, 27, 16, 21, 19, 7, 4, 5, 15, 3, 9, 2, 17],
    [10, 6, 22, 18, 23, 20, 13, 3, 5, 15, 12, 11, 0, 1, 24, 26, 4, 19, 7, 25, 8, 14, 27, 16, 21, 17, 9, 2],
    [13, 1, 11, 6, 21, 17, 3, 23, 10, 20, 8, 2, 24, 0, 14, 15, 26, 5, 19, 18, 9, 4, 27, 7, 12, 25, 16, 22]]

@[expose] def burnsideF48s_g22LetL (l : Fin 6 × Bool) : List ℕ :=
  (if l.2 then burnsideF48s_g22GL else burnsideF48s_g22GLi).getD l.1 []

@[expose] def burnsideF48s_g22EvL (w : List (Fin 6 × Bool)) : List ℕ :=
  w.foldl (fun acc l => compL acc (burnsideF48s_g22LetL l)) (List.range 28)

@[expose] def burnsideF48s_g22TL (_ : Unit := ()) : List (List ℕ) :=
  burnsideF48s_g22TW.map fun s => burnsideF48s_g22EvL (burnsideF48s_g22Word s)

@[expose] def burnsideF48s_g22TiL (_ : Unit := ()) : List (List ℕ) :=
  burnsideF48s_g22TW.map fun s => burnsideF48s_g22EvL (burnsideF48s_g22InvW (burnsideF48s_g22Word s))

@[expose] def burnsideF48s_g22P1L (_ : Unit := ()) : List (List ℕ) :=
  burnsideF48s_g22P1W.map fun s => burnsideF48s_g22EvL (burnsideF48s_g22Word s)

@[expose] def burnsideF48s_g22P2L (_ : Unit := ()) : List (List ℕ) :=
  burnsideF48s_g22P2W.map fun s => burnsideF48s_g22EvL (burnsideF48s_g22Word s)

@[expose] def burnsideF48s_g22CheckGens (_ : Unit := ()) : Bool :=
  (List.finRange 6).all fun i => decide (RepL (burnsideF48s_g22GL.getD i []) (burnsideF48s_g22Gen i)) &&
    decide (RepL (burnsideF48s_g22GLi.getD i []) (burnsideF48s_g22Gen i)⁻¹)

@[expose] def burnsideF48s_g22CheckRels (_ : Unit := ()) : Bool :=
  ((burnsideF48s_g22RelP1 ++ burnsideF48s_g22RelP2).all fun s =>
    decide (burnsideF48s_g22EvL (burnsideF48s_g22Word s) = List.range 28)) &&
  decide (burnsideF48s_g22EvL (burnsideF48s_g22Cand 1) = List.range 28)

@[expose] def burnsideF48s_g22CheckLetters (_ : Unit := ()) : Bool :=
  ((burnsideF48s_g22TW).all fun s => (burnsideF48s_g22Word s).all fun l =>
    decide (l.1 ≠ 3 ∧ l.1 ≠ 4)) &&
  ((burnsideF48s_g22P1W ++ burnsideF48s_g22RelP1 ++ ["bTY"]).all fun s =>
    (burnsideF48s_g22Word s).all fun l => decide (l.1 ≠ 3)) &&
  ((burnsideF48s_g22P2W ++ burnsideF48s_g22RelP2 ++ burnsideF48s_g22CandV).all fun s =>
    (burnsideF48s_g22Word s).all fun l => decide (l.1 ≠ 4))

@[expose] def burnsideF48s_g22CheckClosed (_ : Unit := ()) : Bool :=
  let TL := burnsideF48s_g22TL ()
  let P1L := burnsideF48s_g22P1L ()
  let P2L := burnsideF48s_g22P2L ()
  decide (burnsideF48s_g22TW.length = 64) && decide (burnsideF48s_g22P1W.length = 192) &&
  decide (burnsideF48s_g22P2W.length = 192) &&
  decide (burnsideF48s_g22TW.getD 0 "x" = "") && decide (burnsideF48s_g22P1W.getD 0 "x" = "") &&
  decide (burnsideF48s_g22P2W.getD 0 "x" = "") &&
  ((List.range 64).all fun i => [0, 1, 2, 5].all fun g =>
    (List.range 64).any fun j =>
      decide (compL (TL.getD i []) (burnsideF48s_g22GL.getD g []) = TL.getD j [])) &&
  ((List.range 192).all fun i => [0, 1, 2, 4, 5].all fun g =>
    (List.range 192).any fun j =>
      decide (compL (P1L.getD i []) (burnsideF48s_g22GL.getD g []) = P1L.getD j [])) &&
  ((List.range 192).all fun i => [0, 1, 2, 3, 5].all fun g =>
    (List.range 192).any fun j =>
      decide (compL (P2L.getD i []) (burnsideF48s_g22GL.getD g []) = P2L.getD j [])) &&
  ((List.range 64).all fun i => (List.range 64).all fun j =>
    !(decide (TL.getD i [] = TL.getD j [])) || decide (i = j))

@[expose] def burnsideF48s_g22CheckCand (_ : Unit := ()) : Bool :=
  let TL := burnsideF48s_g22TL ()
  let TiL := burnsideF48s_g22TiL ()
  let P1L := burnsideF48s_g22P1L ()
  let P2L := burnsideF48s_g22P2L ()
  let UL := burnsideF48s_g22EvL (burnsideF48s_g22Word "bTY")
  let VL := burnsideF48s_g22CandV.map fun s => burnsideF48s_g22EvL (burnsideF48s_g22Word s)
  (List.range 192).all fun i =>
    !(decide (compL (P1L.getD i []) (P1L.getD i []) = List.range 28) &&
      (List.range 64).all fun t => decide (P1L.getD i [] ≠ TL.getD t [])) ||
    (List.range 192).all fun j =>
      !(decide (compL (P2L.getD j []) (P2L.getD j []) = List.range 28) &&
        (List.range 64).all fun t => decide (P2L.getD j [] ≠ TL.getD t [])) ||
      (List.range 64).any fun t => (List.range 4).any fun k =>
        decide (compL (compL (TL.getD t []) (P1L.getD i [])) (TiL.getD t []) = UL) &&
        decide (compL (compL (TL.getD t []) (P2L.getD j [])) (TiL.getD t []) = VL.getD k [])

end CFSG.ASVolI

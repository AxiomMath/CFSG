module

public import Certificates.Data.CFSGNative.J4Tree.Aff
public import Certificates.Data.CFSGNative.J4Tree.Index
public import Certificates.Data.CFSGNative.J4Tree.Node
public import Certificates.Data.CFSGNative.J4Tree.VerdictJ

public section

namespace CFSG.J4Tree.M4

open CFSG.Sporadic.J4.Native CFSG.J4Tree.Native CFSG.J4Tree.Native.Node CFSG.J4Tree.VerdictJ

set_option compiler.extract_closed false

@[expose] def kGens : List (Nat × Nat) :=
  [(841, 1014), (1076, 478), (145, 240), (751, 608), (218, 776), (421, 6), (984, 926), (930, 616),
    (1079, 926), (1490, 182)]

@[expose] def fBasis : List (Nat × Nat) :=
  [(1834, 608), (1198, 32), (734, 176), (1056, 944), (206, 608), (141, 0), (705, 0), (1796, 0),
    (871, 0), (8, 0)]

@[expose] def gWord : List Int :=
  [3, -1, -3, 1, 1, -2, 1, -3, 1, 3, -1, -2, -1, -3, 1, 2, -1, -3, 1, 3, 2, -1, 3, 2, 2, -1, -3,
    -3]

@[expose] def sextMasks : List Nat := [133, 778, 911, 1131, 1262, 1889, 2020]

@[expose] def y136 : List (Nat × Nat) := [(183, 984), (1131, 0), (326, 576), (824, 984)]

@[expose] def y266 : List (Nat × Nat) := [(1889, 0), (1131, 0), (588, 576), (713, 576)]

@[expose] def o136 : List Nat := [2, 8, 10, 16, 18, 24, 26, 128, 130, 136, 138, 144, 146, 152, 154]

@[expose] def o266 : List Nat :=
  [31, 36, 59, 76, 83, 104, 119, 139, 148, 175, 176, 199, 216, 227, 252]

@[expose] def yin136 : List Nat := [2, 8, 16, 128]

@[expose] def yin266 : List Nat := [31, 36, 76, 139]

@[expose] def h136 : Nat × Nat := (1236, 70)

@[expose] def h266 : Nat × Nat := (656, 912)

@[expose] def rounds : Nat := 64

@[expose] def closureOf (gs : List Code) : Std.HashSet Code := bfsFrom gs rmul 1 rounds

@[expose] def subOK (gs : List Code) (S : Std.HashSet Code) : Bool :=
  S.contains 1 && closedUnder gs rmul S

@[expose] def pairsOf (gs : List Code) : List (Code × Code) := gs.map fun g => (g, g.inv)

@[expose] def pairsOK (gp : List (Code × Code)) : Bool :=
  gp.all fun p => p.1 * p.2 == 1 && p.2.wf

@[expose] def orbitOf (gp : List (Code × Code)) (x : Code) : Std.HashSet Code :=
  bfsFrom gp conjP x rounds

@[expose] def orbOK (gp : List (Code × Code)) (x : Code) (O : Std.HashSet Code) : Bool :=
  O.contains x && closedUnder gp conjP O

@[noinline, expose] def classCore (gp : List (Code × Code)) (F : Std.HashSet Code) (x : Code)
    (O : Std.HashSet Code) : Bool :=
  orbOK gp x O && (O.size != 4 || F.contains x)

@[expose] def classOK (gp : List (Code × Code)) (F : Std.HashSet Code) (x : Code) : Bool :=
  x * x != 1 || classCore gp F x (orbitOf gp x)

@[noinline, expose] def basisCore (gp : List (Code × Code)) (b : Code) (O : Std.HashSet Code) :
    Bool :=
  orbOK gp b O && O.size == 4

@[expose] def basisClassOK (gp : List (Code × Code)) (b : Code) : Bool :=
  b * b == 1 && basisCore gp b (orbitOf gp b)

@[expose] def maskCodeL (L : List (Nat × Nat)) (m : Nat) : Code :=
  (List.range L.length).foldl (fun acc l => if m.testBit l then acc * cc (L.getD l (0, 0)) else acc)
    1

@[noinline, expose] def yCore (Y : Std.HashSet Code) (yg : List Code) (y w : List (Nat × Nat))
    (yin os : List Nat) : Bool :=
  subOK yg Y && y.length == yin.length &&
    (List.range y.length).all (fun i => cc (y.getD i (0, 0)) == maskCodeL w (yin.getD i 0) &&
      os.contains (yin.getD i 0)) &&
    os.all fun o => Y.contains (maskCodeL w o)

@[expose] def yOK (y w : List (Nat × Nat)) (yin os : List Nat) : Bool :=
  yCore (closureOf (y.map cc)) (y.map cc) y w yin os

@[expose] def coordsOK (L : List (Nat × Nat)) : Bool := L.all fun p => decide (p.2 < 1024)

@[noinline, expose] def k539OK (K F W R : Std.HashSet Code) (kg fg wg rg : List Code)
    (gp : List (Code × Code)) (gc gci : Code) : Bool :=
  subOK kg K && subOK fg F && subOK wg W && subOK rg R && K.size == 16384 &&
    rg.all W.contains && wg.all R.contains &&
    kg.all (fun k => wg.all fun w => k * w == w * k) &&
    fg.all K.contains && fg.all (· != 1) && pairsOK gp &&
    K.toList.all (classOK gp F) && fg.all (basisClassOK gp) &&
    gc * gci == 1 && gci.wf && fg.all (fun b => F.contains (gc * b * gci)) &&
    wg.any (fun w => !W.contains (gc * w * gci)) &&
    sextMasks.all fun c => W.contains (etaCode c)

@[expose] def hOK (h : Code) (yg wg : List Code) : Bool :=
  yg.all (fun y => h * y == y * h) && wg.any (fun w => h * w != w * h)

@[expose] def codeChecks (_ : Unit := ()) : Bool :=
  treeOrd 539 == 16384 && coordsOK kGens && coordsOK fBasis && coordsOK (treeWv 539) &&
    coordsOK (treeBasis 539) &&
    coordsOK y136 && coordsOK y266 && coordsOK [h136, h266] && coordsOK (treeWv 136) &&
    coordsOK (treeWv 266) &&
    k539OK (closureOf (kGens.map cc)) (closureOf (fBasis.map cc)) (closureOf ((treeWv 539).map cc))
      (closureOf ((treeBasis 539).map cc)) (kGens.map cc) (fBasis.map cc) ((treeWv 539).map cc)
      ((treeBasis 539).map cc) (pairsOf (kGens.map cc)) (codeOfWord gWord)
      (codeOfWord gWord).inv &&
    hOK (cc h136) (y136.map cc) ((treeWv 136).map cc) &&
    hOK (cc h266) (y266.map cc) ((treeWv 266).map cc) &&
    yOK y136 (treeWv 136) yin136 o136 && yOK y266 (treeWv 266) yin266 o266

structure ConjD where
  word : List Int
  tgt : List (Nat × Nat)
  fwd : List Nat
  bwd : List Nat

@[noinline, expose] def conjCore (G : Array V2) (S T : Array (Array V2)) (fwd bwd : List Nat) :
    Bool :=
  fwd.length == S.size && bwd.length == T.size &&
    (List.range S.size).all (fun i => eqRows (mulRows G (S[i]?.getD idRows))
      (mulRows (maskRows T (fwd.getD i 0)) G)) &&
    (List.range T.size).all fun j => eqRows (mulRows (T[j]?.getD idRows) G)
      (mulRows G (maskRows S (bwd.getD j 0)))

@[expose] def conjOK (X : Ctx) (src : List (Nat × Nat)) (d : ConjD) : Bool :=
  coordsOK src && coordsOK d.tgt &&
    conjCore (eltRows X [("", d.word)]) (src.map (coordRows X)).toArray
      (d.tgt.map (coordRows X)).toArray d.fwd d.bwd

@[expose] def c486 : ConjD := ⟨[16, 16, 14], treeWv 486, [9, 12, 3, 8], [9, 13, 10, 8]⟩

@[expose] def c542 : ConjD := ⟨[14, 16, 23, 16], treeWv 542, [8, 6, 7, 10], [6, 9, 11, 1]⟩

@[expose] def c136 : ConjD := ⟨[16, 29, 16], y136, [1, 11, 5, 12], [1, 14, 5, 13]⟩

@[expose] def c266 : ConjD := ⟨[18], y266, [10, 1, 4, 7], [2, 14, 4, 15]⟩

@[expose] def conjChecks (X : Ctx) : Bool :=
  conjOK X (treeWv 539) c486 && conjOK X (treeWv 539) c542 && conjOK X (treeWv 539) c136 &&
    conjOK X (treeWv 539) c266

end CFSG.J4Tree.M4

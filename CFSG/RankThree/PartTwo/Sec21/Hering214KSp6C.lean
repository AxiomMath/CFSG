module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KSp6R
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCertInputs

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open Sp6R

namespace Sp6Data

@[expose] def zR0 : List ℕ := [8, 2, 4, 9, 16, 32]

@[expose] def zR1 : List ℕ := [1, 16, 4, 8, 18, 32]

@[expose] def zR2 : List ℕ := [1, 2, 32, 8, 16, 36]

@[expose] def tR : List ℕ := [4, 1, 2, 32, 8, 16]

@[expose] def eltR (a b c i : ℕ) : List ℕ :=
  mulR (mulR (mulR (powR zR0 a) (powR zR1 b)) (powR zR2 c)) (powR tR i)

@[expose] def rowsOf (n : ℕ) : List ℕ := (List.range 6).map fun i => (n >>> (6 * i)) &&& 63

@[expose] def codeOfRows (R : List ℕ) : List ℕ :=
  (List.range 36).map fun p => ((R.getD (p / 6) 0).testBit (p % 6)).toNat

@[expose] def clsX : List ℕ :=
  [17322483780, 34630549640, 34630549640, 34630549640, 34630549640, 34663842817, 34663842817,
    34663842817, 34664104968, 34664104968, 34664104968, 34662007817, 34662007817, 34662007817,
    17331921444, 9194444818]

@[expose] def clsY : List ℕ :=
  [38959186952, 34663842817, 38925369473, 38958924801, 38690489473, 38925369473, 38925631624,
    38923534473, 38925369473, 38925631624, 38923534473, 38925369473, 38925631624, 38923534473,
    8661768464, 17206092384]

@[expose] def clsU1 : List ℕ :=
  [0, 13155598501, 34529625619, 24261959937, 7350594689, 34636877992, 8866926764, 5648978089,
    34817459402, 0, 0, 34498167882, 0, 0, 0, 0]

@[expose] def clsU2 : List ℕ :=
  [0, 5648814209, 34416903233, 41173601409, 58085034241, 44293177484, 14236782724, 48588308644,
    34377319952, 0, 0, 34417164889, 0, 0, 0, 0]

@[expose] def clsV : List ℕ :=
  [32, 0, 0, 0, 0, 0, 0, 0, 0, 56, 56, 0, 56, 56, 32, 32]

@[expose] def clsKinv : List ℕ :=
  [2449772836, 0, 0, 0, 0, 0, 0, 0, 0, 50594446590, 8249899002, 0, 8233383867, 49520962815,
    17247274144, 9731383844]

@[expose] def clsWords : List (List ℕ) :=
  [[0, 1, 3, 4, 6, 7], [], [], [], [], [], [], [], [], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [],
    [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]]

@[expose] def isGood (k : ℕ) : Bool := clsU1.getD k 0 != 0

@[expose] def cubeR (A : List ℕ) : List ℕ := mulR (mulR A A) A

@[expose] def wordsXY (X Y : List ℕ) : List (List ℕ) :=
  (List.range 3).flatMap fun e => (List.range 3).map fun f => mulR (powR X e) (powR Y f)

@[expose] def conjR (Z U : List ℕ) : List ℕ := mulR (mulR Z U) (mulR Z Z)

@[expose] def four4B (U1 U2 C : List ℕ) : Bool :=
  C == oneR || C == U1 || C == U2 || C == mulR U1 U2

@[expose] def fourChk (X Y U1 U2 : List ℕ) : Bool :=
  mulR U1 U1 == oneR && mulR U2 U2 == oneR && mulR U1 U2 == mulR U2 U1 && U1 != oneR &&
    U2 != oneR && U1 != U2 && four4B U1 U2 (conjR X U1) && four4B U1 U2 (conjR X U2) &&
    four4B U1 U2 (conjR Y U1) && four4B U1 U2 (conjR Y U2) &&
    (conjR X U1 != U1 || conjR Y U1 != U1)

@[expose] def classChk (k : ℕ) (X Y : List ℕ) : Bool :=
  if isGood k then
    (wordsXY (rowsOf (clsX.getD k 0)) (rowsOf (clsY.getD k 0))).contains X &&
      (wordsXY (rowsOf (clsX.getD k 0)) (rowsOf (clsY.getD k 0))).contains Y &&
      fourChk X Y (rowsOf (clsU1.getD k 0)) (rowsOf (clsU2.getD k 0))
  else
    (wordsXY X Y).contains (rowsOf (clsX.getD k 0)) &&
      (wordsXY X Y).contains (rowsOf (clsY.getD k 0))

@[expose] def xOK (X : List ℕ) : Bool := cubeR X == oneR && X != oneR

@[expose] def pairOK (X Y : List ℕ) : Bool :=
  !(cubeR Y == oneR && mulR X Y == mulR Y X && Y != oneR && Y != X && Y != mulR X X) ||
    (List.range 16).any fun k => classChk k X Y

@[expose] def pairsChk : Bool :=
  (List.range 3).all fun a => (List.range 3).all fun b => (List.range 3).all fun c =>
    (List.range 3).all fun i =>
      !xOK (eltR a b c i) ||
      (List.range 3).all fun a' => (List.range 3).all fun b' => (List.range 3).all fun c' =>
        (List.range 3).all fun i' => pairOK (eltR a b c i) (eltR a' b' c' i')

@[expose] def upairsOK : Bool :=
  (List.range 16).all fun k =>
    !isGood k || (pairCheck (codeOfRows (rowsOf (clsU1.getD k 0)),
        codeOfRows (rowsOf (clsU1.getD k 0))) &&
      pairCheck (codeOfRows (rowsOf (clsU2.getD k 0)), codeOfRows (rowsOf (clsU2.getD k 0))))

@[expose] def cycAll : Bool :=
  (List.range 16).all fun k =>
    isGood k || cycChk (rowsOf (clsX.getD k 0)) (rowsOf (clsY.getD k 0)) (clsWords.getD k [])
      (clsV.getD k 0) (rowsOf (clsKinv.getD k 0))

theorem upairsOK_true : upairsOK = true := by decide +kernel

theorem cycAll_true : cycAll = true := by decide +kernel

theorem pairsChk_true : pairsChk = true := by decide +kernel

end Sp6Data

end CFSG.RankThree.PartTwo.Sec21.Hering214

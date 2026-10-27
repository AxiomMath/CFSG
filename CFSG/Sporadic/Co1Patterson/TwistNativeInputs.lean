module

public import CFSG.Sporadic.Co1Patterson.TwistNativeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridgeData
public import CFSG.Sporadic.Co1Block.IotaBase

public section

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.InvNative
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl CFSG.Monster.B.Co2.Native

@[expose] def twBaseRows : List Rows := [aR, bR, iotaARows] ++ (List.range 8).map iotaQRows

@[expose] def twDerivs : List (List Int) := twDerivsEnc.map decWord

@[expose] def twRows : List Rows := (dag twBaseRows twDerivs).1

@[expose] def twRow (j : Nat) : Rows := twRows.getD (j - 1) one

@[expose] def yBits : List Nat := [1, 2, 57, 155, 8, 7, 98, 181]

@[expose] def qWordRow (e : Nat) : Rows :=
  (List.range 8).foldl (fun acc k => if e.testBit k then mul acc (iotaQRows k) else acc) one

@[expose] def yRow (i : Nat) : Rows := qWordRow (yBits.getD i 0)

@[expose] def yprodRow (c : Nat) : Rows :=
  (List.range 8).foldl (fun acc i => if c.testBit i then mul acc (yRow i) else acc) one

@[expose] def colsApply (m : List Nat) (v : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => if v.testBit i then acc ^^^ m.getD i 0 else acc) 0

@[expose] def colsMul (m n : List Nat) : List Nat :=
  (List.range 8).map fun i => colsApply m (n.getD i 0)

@[expose] def idCols : List Nat := (List.range 8).map (2 ^ ·)

@[expose] def eichCols (j : Nat) : List Nat :=
  let p := (rootPairs.getD j []).getD 0 (0, 0)
  (List.range 8).map fun i => eichNat p.1 p.2 (2 ^ i)

@[expose] def wordCols (w : List Nat) : List Nat :=
  w.foldl (fun acc j => colsMul acc (eichCols j)) idCols

@[expose] def betaCols : List Nat := (List.range 8).map fun i => transNat 17 (2 ^ i)

@[expose] def uWords : List (List Nat) :=
  [[0], [2, 0, 2], [4, 2, 0, 2, 4], [6, 2, 0, 2, 6], [4, 2, 6, 2, 0, 2, 6, 2, 4],
    [2, 4, 6, 2, 0, 2, 6, 4, 2]]

@[expose] def hIdx : List Nat := [67, 68, 69, 70, 71, 72]

@[expose] def kIdx : List Nat := [73, 74]

@[expose] def kCols : List (List Nat) :=
  [[1, 236, 72, 231, 159, 135, 6, 133], [1, 225, 65, 75, 255, 9, 102, 96]]

@[expose] def h4Idx : Nat := 75

@[expose] def h4pIdx : Nat := 76

@[expose] def h4Cols : List Nat := [66, 10, 24, 8, 12, 60, 11, 231]

@[expose] def gIdx : Nat := 83

@[expose] def conjOK (h : Rows) (m : List Nat) : Bool :=
  mul h (inv h) == one && (List.range 8).all fun k =>
    let x := mul (mul h (yRow k)) (inv h)
    x == yprodRow (m.getD k 0) || x == mul (yprodRow (m.getD k 0)) iotaARows

@[noinline, expose] def dagOK : Bool :=
  (dag twBaseRows twDerivs).2.2 && validRows iotaARows &&
    (List.range 8).all (fun i => validRows (yRow i)) &&
    (List.range 256).all (fun c => validRows (yprodRow c)) &&
    (hIdx ++ [h4Idx, h4pIdx]).all fun j => validRows (twRow j)

@[noinline, expose] def yFormOK : Bool :=
  (List.range 256).all fun c =>
    (mul (yprodRow c) (yprodRow c) == one) == !CFSG.EvenSmallLie.OmegaEight.qNat c &&
      (List.range 8).all fun i =>
        (mul (yprodRow c) (yRow ((i + 4) % 8)) == mul (yRow ((i + 4) % 8)) (yprodRow c)) ==
          !c.testBit i

@[noinline, expose] def elemsOK : Bool :=
  ((List.range 6).all fun i =>
      conjOK (twRow (hIdx.getD i 0)) (wordCols (uWords.getD i [])) &&
        mul (twRow (hIdx.getD i 0)) iotaARows == mul iotaARows (twRow (hIdx.getD i 0)) &&
        mul (twRow (hIdx.getD i 0)) (yRow 0) == mul (yRow 0) (twRow (hIdx.getD i 0))) &&
    ((List.range 2).all fun i =>
      conjOK (twRow (kIdx.getD i 0)) (kCols.getD i []) &&
        mul (twRow (kIdx.getD i 0)) iotaARows == mul iotaARows (twRow (kIdx.getD i 0)) &&
        mul (twRow (kIdx.getD i 0)) (yRow 0) == mul (yRow 0) (twRow (kIdx.getD i 0))) &&
    (conjOK (twRow h4Idx) h4Cols &&
      mul (twRow h4Idx) iotaARows == mul iotaARows (twRow h4Idx)) &&
    (conjOK (twRow h4pIdx) (colsMul (colsMul betaCols h4Cols) betaCols) &&
      mul (twRow h4pIdx) iotaARows == mul iotaARows (twRow h4pIdx))

@[expose] def wVecs : List Nat := (List.range 256).filter fun v => !v.testBit 0 && !v.testBit 4

@[expose] def actW (m : List Nat) (v : Nat) : Nat := colsApply m v &&& 254

@[expose] def irrWords : List (List Nat) :=
  [[0], [0, 0], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [1, 0, 0], [1, 0, 1], [1, 1, 0],
    [1, 1, 1]]

@[expose] def actWord (w : List Nat) (v : Nat) : Nat :=
  w.foldr (fun j u => actW (kCols.getD j []) u) v

@[expose] def xorSpan (vs : List Nat) : List Nat := vs.foldl (fun S v => S ++ S.map (· ^^^ v)) [0]

@[noinline, expose] def irrOK : Bool :=
  wVecs.all fun x => x == 0 ||
    (let S := xorSpan (irrWords.map fun w => actWord w x)
     wVecs.all fun t => S.contains t)

@[expose] def mprodCols (c : Nat) : List Nat :=
  (List.range 6).foldl
    (fun acc i => if c.testBit i then colsMul acc (wordCols (uWords.getD i [])) else acc) idCols

@[noinline, expose] def uOK : Bool :=
  ((List.range 64).all fun c => wVecs.all fun v => actW (mprodCols c) v == v) &&
    (List.range 64).all fun c => (List.range 64).all fun c' =>
      colsApply (mprodCols c) 16 != colsApply (mprodCols c') 16 || c == c'

@[expose] def allBools : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBools n).flatMap fun l => [false :: l, true :: l]

@[expose] def candCols (bs : List Bool) (mu : Nat) : List Nat :=
  [1, 2 ^^^ (bs.getD 0 false).toNat, 4 ^^^ (bs.getD 1 false).toNat,
    8 ^^^ (bs.getD 2 false).toNat, mu, 32 ^^^ (bs.getD 3 false).toNat,
    64 ^^^ (bs.getD 4 false).toNat, 128 ^^^ (bs.getD 5 false).toNat]

@[expose] def isoCols (m : List Nat) : Bool :=
  (List.range 8).all fun j =>
    CFSG.EvenSmallLie.OmegaEight.qNat (m.getD j 0) ==
        CFSG.EvenSmallLie.OmegaEight.qNat (2 ^ j) &&
      (List.range 8).all fun k =>
        bNat (m.getD j 0) (m.getD k 0) == bNat (2 ^ j) (2 ^ k)

@[noinline, expose] def uSetOK : Bool :=
  (allBools 6).all fun bs => (List.range 256).all fun mu =>
    !isoCols (candCols bs mu) || (List.range 64).any fun c =>
      (List.range 8).all fun k => (mprodCols c).getD k 0 == (candCols bs mu).getD k 0

@[noinline, expose] def h4OK : Bool :=
  ((List.range 256).all fun c =>
    mul (mul (twRow h4Idx) (yprodRow c)) (mul (twRow h4Idx) (yprodRow c)) != one &&
      mul (mul (mul (twRow h4Idx) (yprodRow c)) iotaARows)
        (mul (mul (twRow h4Idx) (yprodRow c)) iotaARows) != one) &&
    mul (twRow h4pIdx) (twRow h4pIdx) == one && twRow h4pIdx != one

@[noinline, expose] def nwcOK : Bool :=
  mul (twRow gIdx) (inv (twRow gIdx)) == one &&
    mul (mul (twRow gIdx) iotaARows) (inv (twRow gIdx)) == yRow 0 && yRow 0 != iotaARows

@[expose] def rhoPow : Nat → Nat → Nat
  | 0, j => j
  | k + 1, j => rhoPerm.getD (rhoPow k j) 0

@[expose] def liftLetter (k j : Nat) : Nat := rhoPow ((3 - k) % 3) j

@[expose] def liftRoots (k c : Nat) : List Nat :=
  (List.range 6).flatMap fun i =>
    if c.testBit i then (uWords.getD i []).flatMap fun j => omWords.getD (liftLetter k j) []
    else []

@[expose] def liftSq (k c : Nat) : Array Nat :=
  compA 240 (wordArr (liftRoots k c)) (wordArr (liftRoots k c))

@[noinline, expose] def signOK : Bool :=
  [1, 2].all fun k => (List.range 64).all fun c =>
    eqA 240 (liftSq k c) negArr || eqA 240 (liftSq k c) (idA 240)

@[expose] def aList : List (Nat × Nat) :=
  ((List.range 256).filter fun c => !c.testBit 4).flatMap fun c => [(c, 0), (c, 1)]

@[expose] def aRowOf (p : Nat × Nat) : Rows :=
  if p.2 = 1 then mul (yprodRow p.1) iotaARows else yprodRow p.1

@[expose] def hprodRow (c : Nat) : Rows :=
  (List.range 6).foldl (fun acc i => if c.testBit i then mul acc (twRow (hIdx.getD i 0)) else acc)
    one

@[expose] def countTw (k t : Nat) : Nat :=
  ((List.range 64).map fun c =>
    let s := eqA 240 (liftSq k c) negArr
    let hc := hprodRow c
    (aList.filter fun p =>
      let x := mul hc (aRowOf p)
      if t = 0 then (mul x x == iotaARows && !s) || (mul x x == one && s)
      else (mul x x == yRow 0 && !s) || (mul x x == mul (yRow 0) iotaARows && s)).length).sum

@[noinline, expose] def countOK : Bool :=
  countTw 1 0 == 3136 && countTw 1 1 == 4032 && countTw 2 0 == 3136 && countTw 2 1 == 4032

end CFSG.Sporadic.Co1Patterson.TwistNative

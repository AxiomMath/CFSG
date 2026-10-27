module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXSpec
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.NormNum

public section

namespace CFSG.KC.EvenSporDS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81

@[expose] def insN (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insN a l

@[expose] def isortN : List Nat → List Nat
  | [] => []
  | b :: l => insN b (isortN l)

@[expose] def idColsK : Array Nat := #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512]

@[expose] def composeK (c c' : Array Nat) : Array Nat :=
  #[lin c c'[0]!, lin c c'[1]!, lin c c'[2]!, lin c c'[3]!, lin c c'[4]!, lin c c'[5]!,
    lin c c'[6]!, lin c c'[7]!, lin c c'[8]!, lin c c'[9]!]

@[expose] def fcMatEqLin (m a r : Array Nat) : Bool :=
  m[0]! == lin a r[0]! && m[1]! == lin a r[1]! && m[2]! == lin a r[2]! && m[3]! == lin a r[3]! &&
    m[4]! == lin a r[4]! && m[5]! == lin a r[5]! && m[6]! == lin a r[6]! &&
    m[7]! == lin a r[7]! && m[8]! == lin a r[8]! && m[9]! == lin a r[9]!

@[expose] def idxL (ms : List (Array Nat)) (r : Array Nat) : Nat := ms.findIdx (fcMatEq r)

@[expose] def tabL (ms : List (Array Nat)) : List (List Nat) :=
  ms.map fun a => ms.map fun r => ms.findIdx fun m => fcMatEqLin m a r

@[expose] def keyA (c : Array Nat) : Nat :=
  c[0]! + 1024 * (c[1]! + 1024 * (c[2]! + 1024 * (c[3]! + 1024 * (c[4]! + 1024 * (c[5]! +
    1024 * (c[6]! + 1024 * (c[7]! + 1024 * (c[8]! + 1024 * c[9]!))))))))

@[expose] def colK : Nat → Nat → Nat
  | k, 0 => k % 1024
  | k, i + 1 => colK (k / 1024) i

@[expose] def linK (ka v : Nat) : Nat :=
  (List.range 10).foldr (fun i acc => if v.testBit i then colK ka i ^^^ acc else acc) 0

@[expose] def prodK (ka kr : Nat) : Nat :=
  linK ka (colK kr 0) + 1024 * (linK ka (colK kr 1) + 1024 * (linK ka (colK kr 2) + 1024 *
    (linK ka (colK kr 3) + 1024 * (linK ka (colK kr 4) + 1024 * (linK ka (colK kr 5) + 1024 *
    (linK ka (colK kr 6) + 1024 * (linK ka (colK kr 7) + 1024 * (linK ka (colK kr 8) + 1024 *
    linK ka (colK kr 9)))))))))

@[expose] def tabK (K : List Nat) : List (List Nat) :=
  K.map fun a => K.map fun r => K.idxOf (prodK a r)

@[expose] def getT (T : List (List Nat)) (i j : Nat) : Nat := (T.getD i []).getD j 0

@[expose] def hitsL (ia : List Nat) (n : Nat) : List Nat := (List.range n).filter fun x => ia.contains x

@[expose] def coverL (T : List (List Nat)) (A B : List Nat) (n : Nat) : Bool :=
  (List.range n).all fun i => A.any fun x => B.any fun y => getT T x y == i

@[expose] def extL (T : List (List Nat)) (Y : List Nat) (y : Nat) : List Nat :=
  isortN (Y ++ Y.map fun x => getT T y x)

@[expose] def extOKL (T : List (List Nat)) (e n : Nat) (fam : List (List Nat)) : Bool :=
  fam.all fun Y => (List.range n).all fun y =>
    !(getT T y y == e && !Y.contains y && Y.all fun x => getT T y x == getT T x y) ||
      fam.contains (extL T Y y)

@[expose] def fixL (ms : List (Array Nat)) (Z : List Nat) : Nat :=
  ((List.range 1024).filter fun v => Z.all fun x => lin (ms.getD x #[]) v == v).length

@[expose] def fixOKL (ms : List (Array Nat)) (e : Nat) (fam : List (List Nat)) : Bool :=
  fam.all fun Z => Z == [e] || decide (Z.length * fixL ms Z ≤ 2 ^ 9)

@[expose] def axFixOKL (ms : List (Array Nat)) (q : Nat → Bool) (fam : List (List Nat)) : Bool :=
  fam.all fun Z => Z.all q || decide (Z.length * fixL ms Z ≤ 2 ^ 8)

@[expose] def tabAllL (T : List (List Nat)) (n : Nat) : Bool := T.all (·.all (· < n))

@[expose] def fcRestL (cu cw ms : List (Array Nat)) (fam : List (List Nat))
    (T : List (List Nat)) : Bool :=
  let e := idxL ms idColsK
  let ia := cu.map (idxL ms)
  let ib := cw.map (idxL ms)
  cu.all fcColsLt && cw.all fcColsLt && ms.all fcColsLt && decide (2 ^ 7 ≤ ms.length) &&
    ia.all (· < ms.length) && ib.all (· < ms.length) &&
    coverL T (hitsL ia ms.length) (hitsL ib ms.length) ms.length && decide (e < ms.length) &&
    fam.contains [e] && extOKL T e ms.length fam

@[expose] def axRestL (ms : List (Array Nat)) (fam : List (List Nat)) (T : List (List Nat)) :
    Bool :=
  let e := idxL ms idColsK
  decide (ms.length = 2 ^ 8) && ms.all fcColsLt && decide (e < ms.length) && fam.contains [e] &&
    extOKL T e ms.length fam

@[expose] def axWordColsK (gc : Array (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldr (fun k acc => composeK gc[k]! acc) idColsK

@[expose] def axWordsOKL (gc : Array (Array Nat)) (qs : Array Bool) (ws : Array (List Nat))
    (ms : Array (Array Nat)) : Bool :=
  gc.toList.all fcColsLt && decide (ws.size = ms.size) &&
    (List.range ms.size).all fun j =>
      ws[j]!.all (· < gc.size) && fcMatEq (axWordColsK gc ws[j]!) ms[j]! &&
        (!qs[j]! || ws[j]!.all (· < 9))

end CFSG.KC.EvenSporDS81

module

public import CFSG.Quasithin.H13.L32NMat8Inputs

public section

namespace CFSG.Quasithin.H13.G9MCert

open Mat8Cert

@[expose] def blk (xs : List ℕ) : List ℕ := xs ++ xs.map fun c => 16 * c

@[expose] def s0c : List ℕ := [1, 2, 4, 8, 17, 34, 68, 136]

@[expose] def s1c : List ℕ := [16, 32, 64, 128, 1, 2, 4, 8]

@[expose] def one4 : List ℕ := [1, 2, 4, 8]

@[expose] def all4 : List (List ℕ) :=
  (List.range 16).flatMap fun a => (List.range 16).flatMap fun b =>
    (List.range 16).flatMap fun c => (List.range 16).map fun d => [a, b, c, d]

@[expose] def pow8 (A : List ℕ) : ℕ → List ℕ
  | 0 => one8
  | n + 1 => mul8 A (pow8 A n)

@[expose] def invs : List (List ℕ) := all4.filter fun x => mul8 (blk x) (blk x) == one8

@[expose] def ords5 : List (List ℕ) :=
  all4.filter fun y => pow8 (blk y) 5 == one8 && blk y != one8

@[expose] def relS5 (X Y : List ℕ) : Bool :=
  pow8 (mul8 X Y) 4 == one8 && pow8 (mul8 (mul8 (mul8 X (pow8 Y 4)) X) Y) 3 == one8 &&
    pow8 (mul8 (mul8 (mul8 X (pow8 Y 3)) X) (pow8 Y 2)) 2 == one8

@[expose] def relA5 (X Y : List ℕ) : Bool := pow8 (mul8 X Y) 3 == one8

abbrev Model : Type := List ℕ × List ℕ × List (List ℕ) × List ℕ

@[expose] def modelsS5 : List Model :=
  [([3, 2, 9, 7], [6, 11, 7, 9], [[], [0], [1], [1, 0]], [1, 3, 7, 14]),
    ([1, 8, 4, 2], [6, 12, 5, 4], [[], [1], [0, 1], [1, 1]], [1, 15, 13, 9])]

@[expose] def modelsA5 : List Model :=
  [([10, 15, 9, 14], [5, 10, 14, 7], [[], [0], [1], [1, 0]], [1, 14, 5, 12]),
    ([5, 12, 4, 6], [6, 12, 5, 4], [[], [0], [1], [0, 1]], [1, 7, 3, 8])]

@[expose] def inv4 (c : List ℕ) : Option (List ℕ) :=
  one4.mapM fun b => (List.range 16).find? fun u => mv8 c u == b

@[expose] def verifyC (x y c ic xm ym : List ℕ) : Bool :=
  validB (blk c) && validB (blk ic) && mul8 (blk c) (blk ic) == one8 &&
    mul8 (blk ic) (blk c) == one8 && mul8 (blk x) (blk c) == mul8 (blk c) (blk xm) &&
    mul8 (blk y) (blk c) == mul8 (blk c) (blk ym) && mul8 (blk c) s0c == mul8 s0c (blk c) &&
    mul8 (blk c) s1c == mul8 s1c (blk c)

@[expose] def spinMat (x y : List ℕ) (m : Model) (v : ℕ) : List ℕ :=
  mul8 (m.2.2.1.map fun w => mv8 (evalW [blk x, blk y] w) v) m.2.2.2

@[expose] def tryC (x y : List ℕ) (m : Model) (c : List ℕ) :
    Option (List ℕ × List ℕ × List ℕ × List ℕ) :=
  if mul8 (blk x) (blk c) == mul8 (blk c) (blk m.1) then
    match inv4 c with
    | some ic => if verifyC x y c ic m.1 m.2.1 then some (c, ic, m.1, m.2.1) else none
    | none => none
  else none

@[expose] def findConj (x y : List ℕ) (ms : List Model) :
    Option (List ℕ × List ℕ × List ℕ × List ℕ) :=
  ms.findSome? fun m => (List.range 15).findSome? fun i => tryC x y m (spinMat x y m (i + 1))

@[expose] def y0 : List ℕ := [2, 4, 8, 15]

@[expose] def spinY (y : List ℕ) : List ℕ :=
  let v₁ := mv8 y 1
  let v₂ := mv8 y v₁
  [1, v₁, v₂, mv8 y v₂]

@[expose] def verifyY (y d di : List ℕ) : Bool :=
  validB (blk d) && validB (blk di) && mul8 (blk d) (blk di) == one8 &&
    mul8 (blk di) (blk d) == one8 && mul8 (blk y) (blk d) == mul8 (blk d) (blk y0) &&
    mul8 (blk d) s0c == mul8 s0c (blk d) && mul8 (blk d) s1c == mul8 s1c (blk d)

@[expose] def normCheck : Bool :=
  ords5.all fun y =>
    match inv4 (spinY y) with
    | some di => verifyY y (spinY y) di
    | none => false

@[expose] def s5Check : Bool :=
  invs.all fun x => !relS5 (blk x) (blk y0) || (findConj x y0 modelsS5).isSome

@[expose] def a5Check : Bool :=
  invs.all fun x => x == one4 || !relA5 (blk x) (blk y0) || (findConj x y0 modelsA5).isSome

@[expose] def g9mCheck : Bool := normCheck && s5Check && a5Check

end CFSG.Quasithin.H13.G9MCert

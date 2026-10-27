module

public section

namespace Certificates.S8DFin

structure M8 where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
  c6 : Nat
  c7 : Nat

@[expose] def M8.ap (m : M8) (n : Nat) : Nat :=
  (if n.testBit 0 then m.c0 else 0) ^^^ (if n.testBit 1 then m.c1 else 0) ^^^
    (if n.testBit 2 then m.c2 else 0) ^^^ (if n.testBit 3 then m.c3 else 0) ^^^
    (if n.testBit 4 then m.c4 else 0) ^^^ (if n.testBit 5 then m.c5 else 0) ^^^
    (if n.testBit 6 then m.c6 else 0) ^^^ (if n.testBit 7 then m.c7 else 0)

@[expose] def M8.iter (m : M8) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => m.ap (m.iter k n)

@[expose] def cnib (t : Nat) : Nat := if t < 8 then 2 * t else (2 * t - 16) ^^^ 15

@[expose] def cmul (n : Nat) : Nat := cnib (n % 16) + 16 * cnib (n / 16)

@[expose] def mk (x y : Nat) : M8 :=
  let x1 := cmul x
  let x2 := cmul x1
  let y1 := cmul y
  let y2 := cmul y1
  ⟨x, x1, x2, cmul x2, y, y1, y2, cmul y2⟩

@[expose] def cM : M8 := ⟨2, 4, 8, 15, 32, 64, 128, 240⟩

@[expose] def rV : M8 := ⟨1, 2, 8, 15, 16, 32, 128, 240⟩

@[expose] def rVi : M8 := ⟨1, 2, 15, 4, 16, 32, 240, 64⟩

@[expose] def commAt (F : M8) (n : Nat) : Bool :=
  rV.ap (F.ap (rVi.ap (F.iter 4 (cM.ap n)))) == F.iter 4 (cM.ap (rV.ap (F.ap (rVi.ap n))))

@[expose] def sols : List (Nat × Nat) :=
  [(1, 16), (1, 32), (1, 35), (2, 16), (2, 19), (2, 32), (49, 32), (50, 16), (183, 203),
    (188, 123)]

@[expose] def okXY (x y : Nat) : Bool :=
  let F := mk x y
  !(F.iter 5 1 == 1 && F.iter 5 16 == 16 && [1, 2, 4, 8, 16, 32, 64, 128].all (commAt F)) ||
    sols.contains (x, y)

@[expose] def check (_ : Unit := ()) : Bool :=
  (List.range 256).all fun x => (List.range 256).all fun y => okXY x y

end Certificates.S8DFin

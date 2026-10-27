module

public import Certificates.Data.Kernel.Co2I301.Six

public section

namespace CFSG.KC.Co2I301

open CFSG.KC.Enum

@[expose] noncomputable def vv (P y : Nat) : Nat :=
  nIf(Nat.beq y (nat_lit 0), nat_lit 0, Nat.succ (pt P (Nat.pred y)))

@[expose] noncomputable def bit (m i : Nat) : Nat := fld(m, i, nat_lit 1)

@[expose] noncomputable def xb6 (a0 a1 a2 a3 a4 a5 m : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.mul (bit m (nat_lit 0)) a0)
    (Nat.mul (bit m (nat_lit 1)) a1)) (Nat.mul (bit m (nat_lit 2)) a2))
    (Nat.mul (bit m (nat_lit 3)) a3)) (Nat.mul (bit m (nat_lit 4)) a4))
    (Nat.mul (bit m (nat_lit 5)) a5)

@[expose] noncomputable def par6 (z : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor z (Nat.shiftRight z (nat_lit 1)))
    (Nat.shiftRight z (nat_lit 2))) (Nat.shiftRight z (nat_lit 3)))
    (Nat.shiftRight z (nat_lit 4))) (Nat.shiftRight z (nat_lit 5))) (nat_lit 1)

@[expose] noncomputable def formJ (j0 j1 j2 j3 j4 j5 u v : Nat) : Nat :=
  par6 (Nat.land u (xb6 j0 j1 j2 j3 j4 j5 v))

@[expose] noncomputable def eqK (f g : Nat → Nat) : Bool :=
  allN (nat_lit 64) fun x => Nat.beq (f x) (g x)

@[expose] noncomputable def linK (P : Nat) : Bool :=
  allN (nat_lit 64) fun a => allN (nat_lit 64) fun b =>
    Nat.beq (vv P (Nat.xor a b)) (Nat.xor (vv P a) (vv P b))

@[expose] noncomputable def formK (F : Nat → Nat → Nat) (f : Nat → Nat) : Bool :=
  allN (nat_lit 64) fun a => allN (nat_lit 64) fun b => Nat.beq (F (f a) (f b)) (F a b)

@[expose] noncomputable def candM (X : Nat) (C : Nat → Nat) (a b c x : Nat) : Nat :=
  xb6 a (vv X a) (vv X (vv X a)) (vv X (vv X (vv X a))) b c (C x)

@[expose] noncomputable def candOK (F : Nat → Nat → Nat) (X D : Nat) (C : Nat → Nat)
    (a b c : Nat) : Bool :=
  bIf(eqK (fun x => candM X C a b c (candM X C a b c (candM X C a b c x))) (fun x => x),
    bIf(eqK (candM X C a b c) (fun x => x), true,
      bIf(eqK (candM X C a b c) (vv D), true,
        bIf(eqK (candM X C a b c) (fun x => vv D (vv D x)), true,
          bIf(formK F (candM X C a b c), false, true)))),
    true)

@[expose] noncomputable def fw (w1 w2 w3 i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), w1, nIf(Nat.beq i (nat_lit 1), w2, w3))

@[expose] noncomputable def fixK (X w1 w2 w3 : Nat) : Bool :=
  allN (nat_lit 64) fun y => bIf(Nat.beq (vv X y) y,
    bIf(Nat.beq y (nat_lit 0), true, bIf(Nat.beq y w1, true, bIf(Nat.beq y w2, true,
      Nat.beq y w3))), true)

@[expose] noncomputable def sixCentK (F : Nat → Nat → Nat) (C : Nat → Nat)
    (P0 P1 X D v0 w1 w2 w3 : Nat) : Bool :=
  bAnd(Nat.blt v0 (nat_lit 64), bAnd(Nat.blt (nat_lit 0) w1, bAnd(Nat.blt w1 (nat_lit 64),
  bAnd(Nat.blt (nat_lit 0) w2, bAnd(Nat.blt w2 (nat_lit 64),
  bAnd(linK P0, bAnd(linK P1, bAnd(formK F (vv P0), bAnd(formK F (vv P1),
  bAnd(Nat.beq (vv X w1) w1, bAnd(Nat.beq (vv X w2) w2, bAnd(fixK X w1 w2 w3,
  bAnd(eqK (candM X C v0 w1 w2) (fun x => x),
    allN (nat_lit 64) fun a => allN (nat_lit 3) fun i => allN (nat_lit 3) fun j =>
      candOK F X D C a (fw w1 w2 w3 i) (fw w1 w2 w3 j))))))))))))))

end CFSG.KC.Co2I301

end

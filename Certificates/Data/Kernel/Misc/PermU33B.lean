module

public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Misc.U33B

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def cube (c : Nat) : Nat := mul 28 c (mul 28 c c)

@[expose] noncomputable def cubeOne (c : Nat) : Bool := Nat.beq (cube c) (one 28)

@[expose] noncomputable def cubeMulAt (E : Nat → Nat) (N i : Nat) : Bool :=
  letB (E i) fun a => impB (cubeOne a) (allN N fun j => letB (E j) fun b =>
    impB (cubeOne b) (cubeOne (mul 28 a b)))

@[expose] noncomputable def cntN (N : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f k))) N

@[expose] noncomputable def zOK (z x y : Nat) : Bool :=
  andB (cubeOne z) (andB (notB (Nat.beq z (one 28))) (andB (cubeOne x) (andB (cubeOne y)
    (Nat.beq z (mul 28 (mul 28 (mul 28 x y) (inv 28 x)) (inv 28 y))))))

@[expose] noncomputable def smallAt (E : Nat → Nat) (N z i : Nat) : Bool :=
  letB (E i) fun a => letB (inv 28 a) fun ai =>
    impB (cubeOne a) (impB (notB (Nat.beq a (one 28))) (impB (notB (Nat.beq a z))
      (impB (notB (Nat.beq ai z)) (Nat.ble (cntN N (fun k => letB (E k) fun g =>
        andB (notB (cubeOne g)) (letB (mul 28 (mul 28 g a) (inv 28 g)) fun c =>
          orB (Nat.beq c a) (Nat.beq c ai)))) 11))))

end CFSG.KC.Misc.U33B

end

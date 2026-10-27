module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.MonsterConv.Perm

public section

namespace CFSG.KC.Fi24FixP

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def walkP (A : Nat → Nat → Nat) (w : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun l _ ih x => strictN (A l x) ih) w v

@[expose] noncomputable def idPl19 (k : Nat) : Nat := idPlane (nat_lit 524288) k

@[expose] noncomputable def fixStep (F : Nat → Nat) (P0 k a : Nat) : Nat :=
  Nat.land a (Nat.xor (ones (nat_lit 524288))
    (Nat.xor (nIf(Nat.beq k (nat_lit 0), P0,
      Nat.xor (F (Nat.xor (idPl19 k) (idPl19 (nat_lit 0)))) P0)) (idPl19 k)))

@[expose] noncomputable def fixAcc (F : Nat → Nat) (P0 k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (ones (nat_lit 306936))
    (fun k acc => strictN acc (fun a => fixStep F P0 k a)) k

@[expose] noncomputable def fixS (F : Nat → Nat) : Nat :=
  strictN (F (idPl19 (nat_lit 0))) (fun P0 => fixAcc F P0 (nat_lit 19))

@[expose] noncomputable def fixOK (A : Nat → Nat → Nat) (w : List Nat) (c : Nat) : Bool :=
  Nat.beq (popcount (fixS (walkP A w)) (nat_lit 524288)) c

end CFSG.KC.Fi24FixP

end

module

public import Certificates.Data.Kernel.Spor.ONK

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def trEq (X j Y i : Nat) : Bool :=
  bAnd(bIf(bit (vP X) j, bit (vP Y) i, Bool.not (bit (vP Y) i)),
    bIf(bit (vM X) j, bit (vM Y) i, Bool.not (bit (vM Y) i)))

@[expose] noncomputable def tposK (R C : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 154) fun i => canon (R i), bAnd(allN (nat_lit 154) fun j => canon (C j),
    allN (nat_lit 154) fun i => strictB (R i) fun x =>
      allN (nat_lit 154) fun j => trEq x j (C j) i))

@[expose] noncomputable def unitK (L : List Nat) (X : Nat → Nat) : Bool :=
  allN (nat_lit 154) fun k => strictB (X k) fun x =>
    bAnd(canon x, Nat.beq (mv L x) (vmk (Nat.shiftLeft (nat_lit 1) k) (nat_lit 0)))

@[expose] noncomputable def imgK (L : List Nat) (C D : Nat → Nat) : Bool :=
  allN (nat_lit 154) fun i => strictB (D i) fun d => bAnd(canon d, Nat.beq (mv L (C i)) d)

@[expose] noncomputable def sigAt (KS K : Nat → Nat) (LT : List Nat) (i : Nat) : Bool :=
  strictB (key KS i) fun s => bAnd(canon s, Nat.beq s (mv LT (key K i)))

@[expose] noncomputable def sigRange (KS K : Nat → Nat) (LT : List Nat) (lo cnt : Nat) : Bool :=
  allBlk lo (sigAt KS K LT) cnt

end CFSG.KS.ON

end

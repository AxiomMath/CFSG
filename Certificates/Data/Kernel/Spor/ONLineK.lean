module

public import Certificates.Data.Kernel.Spor.ONK

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def lead1 (X L : Nat) : Bool :=
  strictB (vP X) fun p => strictB (vM X) fun m =>
    bAnd(Nat.blt L (nat_lit 154), bAnd(bit p L,
      Nat.beq (Nat.land (Nat.lor p m) (Nat.sub (Nat.shiftLeft (nat_lit 1) L) (nat_lit 1)))
        (nat_lit 0)))

@[expose] noncomputable def pmEq (Z Y : Nat) : Bool := bIf(Nat.beq Z Y, true, Nat.beq Y (vneg Z))

@[expose] noncomputable def lineAt (KL LP : Nat → Nat) (LA LB : List Nat) (AL BL : Nat → Nat)
    (n h : Nat) : Bool :=
  strictB (key KL h) fun x => strictB (tab AL h) fun a => strictB (tab BL h) fun b =>
    bAnd(canon x, bAnd(lead1 x (tab LP h), bAnd(Nat.blt a n, bAnd(Nat.blt b n,
      bAnd(pmEq (key KL a) (mv LA x), pmEq (key KL b) (mv LB x))))))

@[expose] noncomputable def lineRange (KL LP : Nat → Nat) (LA LB : List Nat) (AL BL : Nat → Nat)
    (n lo cnt : Nat) : Bool :=
  allBlk lo (lineAt KL LP LA LB AL BL n) cnt

@[expose] noncomputable def piAt (K NEG A B KL AL BL PI : Nat → Nat) (n i : Nat) : Bool :=
  strictB (tab PI i) fun p => bAnd(Nat.blt p n, bAnd(pmEq (key KL p) (key K i),
    bAnd(Nat.beq (tab PI (tab NEG i)) p, bAnd(bIf(Nat.beq (tab NEG i) i, false, true),
      bAnd(Nat.beq (tab PI (tab A i)) (tab AL p), Nat.beq (tab PI (tab B i)) (tab BL p))))))

@[expose] noncomputable def piRange (K NEG A B KL AL BL PI : Nat → Nat) (n lo cnt : Nat) : Bool :=
  allBlk lo (piAt K NEG A B KL AL BL PI n) cnt

@[expose] noncomputable def preAt (PI PRE : Nat → Nat) (N j : Nat) : Bool :=
  strictB (tab PRE j) fun i => bAnd(Nat.blt i N, Nat.beq (tab PI i) j)

@[expose] noncomputable def preRange (PI PRE : Nat → Nat) (N lo cnt : Nat) : Bool :=
  allBlk lo (preAt PI PRE N) cnt

end CFSG.KS.ON

end

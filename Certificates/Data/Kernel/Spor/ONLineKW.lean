module

public import Certificates.Data.Kernel.Spor.ONKW
public import Certificates.Data.Kernel.Spor.ONLineK

public section

namespace CFSG.KS.ONW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def nzW (E LO D : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftRight (Nat.add (Nat.land D LO) LO) (nat_lit 256)) E)
    (Nat.land (Nat.shiftRight (Nat.add (Nat.land (Nat.shiftRight D (nat_lit 256)) LO) LO)
      (nat_lit 256)) E)

@[expose] noncomputable def pmW (E LO ZP ZM YP YM : Nat) : Bool :=
  Nat.beq (Nat.land (nzW E LO (Nat.lor (Nat.xor YP ZP) (Nat.xor YM ZM)))
    (nzW E LO (Nat.lor (Nat.xor YP ZM) (Nat.xor YM ZP)))) (nat_lit 0)

@[expose] noncomputable def wmvLT (E XP XM : Nat) (fin : Nat → Nat → Bool) (L : List Nat) :
    Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ ap am => fin ap am)
    (fun c _ ih j ap am =>
      bAnd(Nat.blt c (Nat.shiftLeft (nat_lit 1) (nat_lit 512)), bAnd(Nat.blt j (nat_lit 512),
        strictB (vP c) fun cp => strictB (vM c) fun cm =>
        strictB (selW XP E j) fun sp => strictB (selW XM E j) fun sm =>
        strictB (Nat.lor (Nat.mul sp cp) (Nat.mul sm cm)) fun tp =>
        strictB (Nat.lor (Nat.mul sp cm) (Nat.mul sm cp)) fun tm =>
        strictB (addP ap am tp tm) fun ap' => strictB (addM ap am tp tm) fun am' =>
          ih (Nat.succ j) ap' am')))
    L

@[expose] noncomputable def finL (LA LB : List Nat) (cnt xk xa xb : Nat) : Bool :=
  strictB (rep (nat_lit 1) cnt) fun E => strictB (rep (mask (nat_lit 256)) cnt) fun LO =>
  strictB (Nat.land xk LO) fun XP => strictB (Nat.land (Nat.shiftRight xk (nat_lit 256)) LO) fun XM =>
    bAnd(wmvLT E XP XM (pmW E LO (Nat.land xa LO) (Nat.land (Nat.shiftRight xa (nat_lit 256)) LO)) LA
        (nat_lit 0) (nat_lit 0) (nat_lit 0),
      wmvLT E XP XM (pmW E LO (Nat.land xb LO) (Nat.land (Nat.shiftRight xb (nat_lit 256)) LO)) LB
        (nat_lit 0) (nat_lit 0) (nat_lit 0))

@[expose] noncomputable def lineRangeW (KL LP : Nat → Nat) (LA LB : List Nat) (AL BL : Nat → Nat)
    (n lo cnt : Nat) : Bool :=
  bAnd(allBlk lo (fun h => lead1 (key KL h) (tab LP h)) cnt,
    ptsW KL AL BL n lo (finL LA LB cnt) cnt (nat_lit 0) (nat_lit 0) (nat_lit 0))

end CFSG.KS.ONW

end

module

public import Certificates.Data.Kernel.Spor.ONKW

public section

namespace CFSG.KS.ONW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def wmvAB (E XP XM GP GM : Nat) (LA : List Nat) :
    List Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Nat → Nat → Bool)
    (fun LB _ ap am => List.rec (motive := fun _ => Bool) (bAnd(Nat.beq ap GP, Nat.beq am GM))
      (fun _ _ _ => false) LB)
    (fun a _ ih LB j ap am => List.rec (motive := fun _ => Bool) false
      (fun b LB' _ =>
        bAnd(Nat.blt a (Nat.shiftLeft (nat_lit 1) (nat_lit 512)),
        bAnd(Nat.blt b (Nat.shiftLeft (nat_lit 1) (nat_lit 512)), bAnd(Nat.blt j (nat_lit 512),
          strictB (Nat.lor (vP a) (Nat.shiftLeft (vP b) (nat_lit 256))) fun cp =>
          strictB (Nat.lor (vM a) (Nat.shiftLeft (vM b) (nat_lit 256))) fun cm =>
          strictB (selW XP E j) fun sp => strictB (selW XM E j) fun sm =>
          strictB (Nat.lor (Nat.mul sp cp) (Nat.mul sm cm)) fun tp =>
          strictB (Nat.lor (Nat.mul sp cm) (Nat.mul sm cp)) fun tm =>
          strictB (addP ap am tp tm) fun ap' => strictB (addM ap am tp tm) fun am' =>
            ih LB' (Nat.succ j) ap' am'))))
      LB)
    LA

@[expose] noncomputable def finAB (LA LB : List Nat) (cnt xk xa xb : Nat) : Bool :=
  strictB (rep (nat_lit 1) cnt) fun E => strictB (rep (mask (nat_lit 256)) cnt) fun LO =>
  strictB (Nat.land xk LO) fun XP => strictB (Nat.land (Nat.shiftRight xk (nat_lit 256)) LO) fun XM =>
    wmvAB E XP XM
      (Nat.lor (Nat.land xa LO) (Nat.shiftLeft (Nat.land xb LO) (nat_lit 256)))
      (Nat.lor (Nat.land (Nat.shiftRight xa (nat_lit 256)) LO)
        (Nat.shiftLeft (Nat.land (Nat.shiftRight xb (nat_lit 256)) LO) (nat_lit 256)))
      LA LB (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def mvRangeAB (K : Nat → Nat) (LA LB : List Nat) (A B : Nat → Nat)
    (n lo cnt : Nat) : Bool :=
  ptsW K A B n lo (finAB LA LB cnt) cnt (nat_lit 0) (nat_lit 0) (nat_lit 0)

end CFSG.KS.ONW

end

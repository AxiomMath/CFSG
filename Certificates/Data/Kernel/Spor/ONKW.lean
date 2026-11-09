module

public import Certificates.Data.Kernel.Spor.ONK

public section

namespace CFSG.KS.ONW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def rep (M cnt : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun _ ih => Nat.add M (Nat.shiftLeft ih (nat_lit 512))) cnt

@[expose] noncomputable def selW (X E j : Nat) : Nat := Nat.land (Nat.shiftRight X j) E

@[expose] noncomputable def wmvL (E XP XM GP GM : Nat) (L : List Nat) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ ap am => bAnd(Nat.beq ap GP, Nat.beq am GM))
    (fun c _ ih j ap am =>
      bAnd(Nat.blt c (Nat.shiftLeft (nat_lit 1) (nat_lit 512)), bAnd(Nat.blt j (nat_lit 512),
        strictB (vP c) fun cp => strictB (vM c) fun cm =>
        strictB (selW XP E j) fun sp => strictB (selW XM E j) fun sm =>
        strictB (Nat.lor (Nat.mul sp cp) (Nat.mul sm cm)) fun tp =>
        strictB (Nat.lor (Nat.mul sp cm) (Nat.mul sm cp)) fun tm =>
        strictB (addP ap am tp tm) fun ap' => strictB (addM ap am tp tm) fun am' =>
          ih (Nat.succ j) ap' am')))
    L

@[expose] noncomputable def finW (LA LB : List Nat) (cnt xk xa xb : Nat) : Bool :=
  strictB (rep (nat_lit 1) cnt) fun E => strictB (rep (mask (nat_lit 256)) cnt) fun LO =>
  strictB (Nat.land xk LO) fun XP => strictB (Nat.land (Nat.shiftRight xk (nat_lit 256)) LO) fun XM =>
    bAnd(wmvL E XP XM (Nat.land xa LO) (Nat.land (Nat.shiftRight xa (nat_lit 256)) LO) LA
        (nat_lit 0) (nat_lit 0) (nat_lit 0),
      wmvL E XP XM (Nat.land xb LO) (Nat.land (Nat.shiftRight xb (nat_lit 256)) LO) LB
        (nat_lit 0) (nat_lit 0) (nat_lit 0))

@[expose] noncomputable def ptsW (K A B : Nat → Nat) (n lo : Nat) (fin : Nat → Nat → Nat → Bool)
    (k : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun xk xa xb => fin xk xa xb)
    (fun k ih xk xa xb =>
      strictB (Nat.add lo k) fun h =>
      strictB (key K h) fun x => strictB (tab A h) fun a => strictB (tab B h) fun b =>
        bAnd(canon x, bAnd(Nat.blt a n, bAnd(Nat.blt b n,
          strictB (Nat.add x (Nat.shiftLeft xk (nat_lit 512))) fun xk' =>
          strictB (Nat.add (key K a) (Nat.shiftLeft xa (nat_lit 512))) fun xa' =>
          strictB (Nat.add (key K b) (Nat.shiftLeft xb (nat_lit 512))) fun xb' =>
            ih xk' xa' xb'))))
    k

@[expose] noncomputable def mvRangeW (K : Nat → Nat) (LA LB : List Nat) (A B : Nat → Nat)
    (n lo cnt : Nat) : Bool :=
  ptsW K A B n lo (finW LA LB cnt) cnt (nat_lit 0) (nat_lit 0) (nat_lit 0)

end CFSG.KS.ONW

end

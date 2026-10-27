module

public import Certificates.Data.Kernel.Spor.ONK

public section

namespace CFSG.KS.ONF

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def recF (T : Nat → Nat) (c xm xp : Nat) : Nat :=
  rget T (nat_lit 4) (nat_lit 15) (nat_lit 448) (mask (nat_lit 448))
    (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft c (nat_lit 4)) xm) (nat_lit 4)) xp)

@[expose] noncomputable def mvFL (T : Nat → Nat) (cnt : Nat) : Nat → Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat)
    (fun _ _ _ ap am => vmk (Nat.shiftRight ap (nat_lit 64)) (Nat.shiftRight am (nat_lit 64)))
    (fun _ ih c xp xm ap am =>
      strictN (recF T c (Nat.land xm (nat_lit 15)) (Nat.land xp (nat_lit 15))) fun e =>
        strictN (Nat.land e (mask (nat_lit 224))) fun ep => strictN (Nat.shiftRight e (nat_lit 224)) fun em =>
          strictN (addP ap am ep em) fun ap' => strictN (addM ap am ep em) fun am' =>
            ih (Nat.succ c) (Nat.shiftRight xp (nat_lit 4)) (Nat.shiftRight xm (nat_lit 4)) ap' am')
    cnt

@[expose] noncomputable def mvF (T : Nat → Nat) (cnt X : Nat) : Nat :=
  strictN (vP X) fun xp => strictN (vM X) fun xm =>
    mvFL T cnt (nat_lit 0) xp xm (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def mvAtF (K : Nat → Nat) (TA TB : Nat → Nat) (cnt : Nat) (A B : Nat → Nat)
    (n h : Nat) : Bool :=
  strictB (key K h) fun x => strictB (tab A h) fun a => strictB (tab B h) fun b =>
    bAnd(canon x, bAnd(Nat.blt a n, bAnd(Nat.blt b n,
      bAnd(Nat.beq (key K a) (mvF TA cnt x), Nat.beq (key K b) (mvF TB cnt x)))))

@[expose] noncomputable def mvRangeF (K : Nat → Nat) (TA TB : Nat → Nat) (cnt : Nat) (A B : Nat → Nat)
    (n lo len : Nat) : Bool :=
  allBlk lo (mvAtF K TA TB cnt A B n) len

@[expose] noncomputable def recOK (T : Nat → Nat) (c : Nat) (C : List Nat) (xm xp : Nat) : Bool :=
  strictB (recF T c xm xp) fun e =>
    Nat.beq (vmk (Nat.shiftRight (Nat.land e (mask (nat_lit 224))) (nat_lit 64))
      (Nat.shiftRight (Nat.shiftRight e (nat_lit 224)) (nat_lit 64))) (mvL C xp xm (nat_lit 0) (nat_lit 0))

@[expose] noncomputable def tabChk (T : Nat → Nat) (CS : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun C _ ih c => bAnd(allBlk (nat_lit 0) (fun xm => allBlk (nat_lit 0) (recOK T c C xm) (nat_lit 16))
      (nat_lit 16), ih (Nat.succ c))) CS

@[expose] noncomputable def lensOK (CS : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun C R ih => bAnd(List.rec (motive := fun _ => Bool) (Nat.ble C.length (nat_lit 4))
      (fun _ _ _ => Nat.beq C.length (nat_lit 4)) R, ih)) CS

@[expose] noncomputable def colsOK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(canon c, ih)) L

end CFSG.KS.ONF

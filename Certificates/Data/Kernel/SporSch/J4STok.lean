module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def tokEq (x : Int) (neg : Bool) (cur : Nat) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun k => bAnd(Nat.beq k cur, bIf(neg, Nat.beq cur (nat_lit 0), true)))
    (fun k => bAnd(neg, Nat.beq (Nat.succ k) cur)) x

@[expose] noncomputable def emitK (neg : Bool) (cur : Nat) (rem : List Int) (k : List Int → Bool) :
    Bool :=
  List.rec (motive := fun _ => Bool) false (fun x xs _ => bAnd(tokEq x neg cur, k xs)) rem

@[expose] noncomputable def nilK (rem : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rem

@[expose] noncomputable def tokRun (cs : List Char) : Nat → Bool → Bool → List Int → Bool :=
  List.rec (motive := fun _ => Nat → Bool → Bool → List Int → Bool)
    (fun cur neg inTok rem => bIf(inTok, emitK neg cur rem nilK, nilK rem))
    (fun ch _ ih cur neg inTok rem => strictB (Char.toNat ch) (fun c =>
      bAnd(Nat.blt c (nat_lit 128),
      bIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
        strictB (Nat.add (Nat.mul cur (nat_lit 10)) (Nat.sub c (nat_lit 48)))
          (fun cur' => ih cur' neg true rem),
        bIf(Nat.beq c (nat_lit 45), ih cur true inTok rem,
          bIf(inTok, emitK neg cur rem (fun r => ih (nat_lit 0) false false r),
            ih (nat_lit 0) false false rem))))))
    cs

@[expose] noncomputable def tokK (cs : List Char) (L : List Int) : Bool :=
  tokRun cs (nat_lit 0) false false L

end CFSG.KS.SporSch

end

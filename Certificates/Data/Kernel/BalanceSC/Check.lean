module

public import Certificates.Data.Kernel.BalanceSC
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.BalanceSC

open CFSG.KC.Enum (pg pcomp strictN strictB)
open CFSG.KS (pinvS)

@[expose] noncomputable def notB (a : Bool) : Bool := bIf(a, false, true)

@[expose] noncomputable def imgMask (n p b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc
      (nIf(Nat.beq (Nat.land (Nat.shiftRight b i) (nat_lit 1)) (nat_lit 1),
        Nat.shiftLeft (nat_lit 1) (pg (nat_lit 4) (nat_lit 15) p i), nat_lit 0))) n

@[expose] noncomputable def memL (c : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun d _ ih => bIf(Nat.beq c d, true, ih)) L

@[expose] noncomputable def anyL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun d _ ih => bIf(f d, true, ih)) L

@[expose] noncomputable def unionL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun d _ ih => Nat.lor d ih) L

@[expose] noncomputable def scAt (L : List Nat) (U c : Nat) : Bool :=
  bAnd(notB (memL c L), notB (Nat.beq (Nat.land c U) (nat_lit 0)))

@[expose] noncomputable def scB (n p : Nat) (L : List Nat) (U : Nat) : Bool :=
  anyL L fun b => strictB (imgMask n p b) (scAt L U)

@[expose] noncomputable def nonOne (x : Nat) : Bool :=
  bIf(Nat.beq x (nat_lit 0), true, notB (Nat.beq (Nat.land x (Nat.sub x (nat_lit 1))) (nat_lit 0)))

@[expose] noncomputable def orthB (n p : Nat) (L : List Nat) : Bool :=
  anyL L fun b => strictB (imgMask n p b) fun c => anyL L fun d => nonOne (Nat.land c d)

@[expose] noncomputable def critB (n : Nat) (o : Bool) (p : Nat) (L : List Nat) (U : Nat) : Bool :=
  bAnd(scB n p L U, bIf(o, orthB n p L, true))

@[expose] noncomputable def pairOK (n N : Nat) (o : Bool) (PT : Nat → Nat) (L : List Nat)
    (U i₁ i₂ : Nat) : Bool :=
  bAnd(Nat.blt i₁ N, bAnd(Nat.blt i₂ N,
    strictB (PT i₁) fun a => strictB (PT i₂) fun b =>
      bAnd(critB n o a L U, bAnd(critB n o b L U,
        strictB (pcomp n (nat_lit 4) (nat_lit 15) a b) fun c => critB n o c L U))))

@[expose] noncomputable def witB (n e w : Nat) : Bool :=
  strictB (pinvS n (nat_lit 4) (nat_lit 15) w) fun wi =>
    strictB (pcomp n (nat_lit 4) (nat_lit 15) w (pcomp n (nat_lit 4) (nat_lit 15) e wi)) fun f =>
      notB (Nat.beq (pcomp n (nat_lit 4) (nat_lit 15) f e) (pcomp n (nat_lit 4) (nat_lit 15) e f))

@[expose] noncomputable def elemOK (n N : Nat) (PT : Nat → Nat) (e i₁ i₂ : Nat) : Bool :=
  bAnd(Nat.blt i₁ N, bAnd(Nat.blt i₂ N,
    strictB (PT i₁) fun a => strictB (PT i₂) fun b =>
      bAnd(witB n e a, bAnd(witB n e b,
        strictB (pcomp n (nat_lit 4) (nat_lit 15) a b) fun c => witB n e c))))

@[expose] noncomputable def packI (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor x (Nat.shiftLeft ih (nat_lit 4))) l

@[expose] noncomputable def zipAll {α β : Type} (f : α → β → Bool) (as : List α) (bs : List β) :
    Bool :=
  List.rec (motive := fun _ => List β → Bool)
    (fun bs => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) bs)
    (fun a _ ih bs => List.rec (motive := fun _ => Bool) false
      (fun b bs' _ => bAnd(f a b, ih bs')) bs) as bs

@[expose] noncomputable def elemsOK (n N : Nat) (PT : Nat → Nat) (L : List Nat)
    (R : List (Nat × Nat)) : Bool :=
  zipAll (fun img pr => strictB (packI img) fun e => elemOK n N PT e pr.1 pr.2) (elemsOf n L) R

@[expose] noncomputable def partRec (n N : Nat) (o : Bool) (PT : Nat → Nat) (L : List Nat)
    (rec : List (Nat × Nat)) : Bool :=
  strictB (unionL L) fun U =>
    bIf(List.rec (motive := fun _ => Bool) false
        (fun pr t _ => bAnd(List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) t,
          pairOK n N o PT L U pr.1 pr.2)) rec,
      true, elemsOK n N PT L rec)

@[expose] noncomputable def partsOK (n r k N : Nat) (S : List Nat) (PT : Nat → Nat)
    (R : List (List (Nat × Nat))) : Bool :=
  zipAll (partRec n N (Nat.beq k r) PT) (chains S k 0) R

@[expose] noncomputable def eqL (a b : List Nat) : Bool :=
  zipAll Nat.beq a b

@[expose] noncomputable def tab64 (T i : Nat) : Nat :=
  fld(T, Nat.shiftLeft i (nat_lit 6), nat_lit 18446744073709551615)

end CFSG.KC.BalanceSC

end

module

public import Certificates.Data.Kernel.Child3

public section

namespace CFSG.KC.J2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3

@[expose] noncomputable def prodCntFrom (n w nb : Nat) (LR TR : Nat → Nat) (f : Nat → Bool) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ g => nIf(f g, nat_lit 1, nat_lit 0))
    (fun _ ih i g => strictN (LR i) (fun R => sumF (rcnt R) (fun a =>
      strictN (pcomp n w (mask w) g (TR (Nat.add (roff n (Nat.mul n w) R) a)))
        (fun h => ih (Nat.succ i) h))))
    nb

@[expose] noncomputable def prodCnt (n w nb : Nat) (LR TR : Nat → Nat) (f : Nat → Bool) : Nat :=
  prodCntFrom n w nb LR TR f (nat_lit 0) (pidn n w)

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def foldList (cnt : Nat) (step : Nat → List Nat → List Nat) (acc : List Nat) :
    List Nat :=
  Nat.rec (motive := fun _ => List Nat) acc (fun a ih => step a ih) cnt

@[expose] noncomputable def prodListFrom (n w nb : Nat) (LR TR : Nat → Nat) (f : Nat → Bool) :
    Nat → Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat → List Nat)
    (fun _ g acc => Bool.rec (motive := fun _ => List Nat) acc (List.cons g acc) (f g))
    (fun _ ih i g acc => strictL (LR i) (fun R => foldList (rcnt R) (fun a acc' =>
      strictL (pcomp n w (mask w) g (TR (Nat.add (roff n (Nat.mul n w) R) a)))
        (fun h => ih (Nat.succ i) h acc')) acc))
    nb

@[expose] noncomputable def prodList (n w nb : Nat) (LR TR : Nat → Nat) (f : Nat → Bool) :
    List Nat :=
  prodListFrom n w nb LR TR f (nat_lit 0) (pidn n w) []

@[expose] noncomputable def prodK (n w : Nat) (ws : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w) (fun X _ ih => pcomp n w (mask w) X ih) ws

@[expose] noncomputable def ordPK (n w m X : Nat) : Bool :=
  bAnd(Nat.beq (ppow n w (mask w) (pidn n w) X m) (pidn n w),
    Nat.rec (motive := fun _ => Bool) true
      (fun d ih => bAnd(ih, bIf(bAnd(Nat.blt (nat_lit 1) d, Nat.beq (Nat.mod m d) (nat_lit 0)),
        bIf(Nat.beq (ppow n w (mask w) (pidn n w) X (Nat.div m d)) (pidn n w), false, true),
        true)))
      (Nat.succ m))

@[expose] noncomputable def allL (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def cntL (f : Nat → Bool) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => strictN ih (fun c => nIf(f x, Nat.succ c, c))) L

@[expose] noncomputable def pairCntK (L M : List Nat) (r : Nat → Nat → Bool) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => strictN ih (fun c => Nat.add c (cntL (r x) M))) L

@[expose] noncomputable def lenL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def ord4K (n w X : Nat) : Bool :=
  strictB (pcomp n w (mask w) X X) (fun X2 =>
    bAnd(Nat.beq (pcomp n w (mask w) X2 X2) (pidn n w), bIf(Nat.beq X2 (pidn n w), false, true)))

end CFSG.KC.J2Cover

end

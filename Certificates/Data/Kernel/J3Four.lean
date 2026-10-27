module

public import Certificates.Data.Kernel.YoshQ.TabN

public section

namespace CFSG.KD.J3Four

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ

@[expose] noncomputable def getN (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def lenN (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def letOK (m : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(Nat.blt a m, ih)) w

@[expose] noncomputable def wImg (G : List Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun a _ ih p => pg (nat_lit 13) (mask (nat_lit 13)) (getN G a) (ih p)) w

@[expose] noncomputable def wInv (Gi : List Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun a _ ih q => ih (pg (nat_lit 13) (mask (nat_lit 13)) (getN Gi a) q)) w

@[expose] noncomputable def keyN (G Gi : List Nat) (x p : Nat) (w : List Nat) : Nat :=
  wInv Gi w (pg (nat_lit 13) (mask (nat_lit 13)) x (wImg G w p))

@[expose] noncomputable def keysN (G Gi : List Nat) (x : Nat) (pts : List Nat) (w : List Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (keyN G Gi x p w) (Nat.shiftLeft ih (nat_lit 13))) pts

@[expose] noncomputable def conjGo (G Gi : List Nat) (x : Nat) (pts : List Nat) (m : Nat) :
    List (Nat × List Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih lo => Prod.rec (motive := fun _ => Bool)
      (fun k w => bAnd(Nat.ble lo k, bAnd(letOK m w,
        bAnd(Nat.beq (keysN G Gi x pts w) k, ih (Nat.succ k))))) r)

@[expose] noncomputable def conjOK (G Gi : List Nat) (x : Nat) (pts : List Nat)
    (R : List (Nat × List Nat)) : Bool :=
  conjGo G Gi x pts (lenN G) R (nat_lit 0)

@[expose] noncomputable def powSq : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih b e acc =>
      strictN (nIf(Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1),
          pmN (nat_lit 6156) (nat_lit 13) b acc, acc)) fun acc' =>
        strictN (pmN (nat_lit 6156) (nat_lit 13) b b) fun b' =>
          ih b' (Nat.shiftRight e (nat_lit 1)) acc')

@[expose] noncomputable def ordOK (x : Nat) (p : Nat) : Bool :=
  bAnd(Nat.blt p (nat_lit 32),
    bAnd(eqN (nat_lit 6156) (nat_lit 13) (powSq (nat_lit 5) x p (pidn (nat_lit 6156) (nat_lit 13)))
      (pidn (nat_lit 6156) (nat_lit 13)),
    bIf(eqN (nat_lit 6156) (nat_lit 13) x (pidn (nat_lit 6156) (nat_lit 13)), false, true)))

@[expose] noncomputable def commAll (t : Nat) (G : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => bAnd(eqN (nat_lit 6156) (nat_lit 13) (pmN (nat_lit 6156) (nat_lit 13) t g)
      (pmN (nat_lit 6156) (nat_lit 13) g t), ih)) G

@[expose] noncomputable def centralOK (G : List Nat) (t : Nat) : Bool :=
  bAnd(commAll t G,
    bAnd(eqN (nat_lit 6156) (nat_lit 13) (pmN (nat_lit 6156) (nat_lit 13) t t)
      (pidn (nat_lit 6156) (nat_lit 13)),
    bIf(eqN (nat_lit 6156) (nat_lit 13) t (pidn (nat_lit 6156) (nat_lit 13)), false, true)))

@[expose] noncomputable def wordN (G : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn (nat_lit 6156) (nat_lit 13))
    (fun a _ ih => pmN (nat_lit 6156) (nat_lit 13) (getN G a) ih) w

@[expose] noncomputable def lenR (R : List (Nat × List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) R

@[expose] noncomputable def rowK (G Gi wx : List Nat) (p : Nat) (pts : List Nat)
    (R : List (Nat × List Nat)) (c : Nat) : Bool :=
  bAnd(Nat.beq (lenR R) c, bAnd(letOK (lenN G) wx,
    strictB (wordN G wx) fun x => bAnd(ordOK x p, conjOK G Gi x pts R)))

end CFSG.KD.J3Four

end

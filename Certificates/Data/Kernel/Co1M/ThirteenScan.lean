module

public import Certificates.Data.Kernel.VecK
public import Certificates.Data.Kernel.SporSch.Co1MatW

public section

namespace CFSG.KD.Co1Thirteen

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.VecK
  CFSG.KS.SporSch.M24

@[expose] noncomputable def eqBB (a b : Bool) : Bool := Bool.rec (notB b) b a

@[expose] noncomputable def lenP (L : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def getP (L : List (Nat × Bool)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a.1 (fun j _ => ih j) i) L

@[expose] noncomputable def memL (L : List Nat) (w : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => orB (Nat.beq a w) ih) L

@[expose] noncomputable def tauK (mem : Nat → Bool) (ts : List (Nat × Bool)) (w : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (eqBB (mem (Nat.xor w (vmF (nat_lit 24) p.1 w))) p.2) ih) ts

@[expose] noncomputable def scanSl (mem : Nat → Bool) (pt : Nat → Nat) (ts : List (Nat × Bool))
    (Q : List Nat) (s : Nat) : Bool :=
  allS (Nat.mul s (nat_lit 256)) (sliceN (nat_lit 98280) (nat_lit 256) s) fun p =>
    strictB (pt p) fun w => orB (notB (tauK mem ts w)) (memL Q w)

@[expose] noncomputable def orbL (T : Nat) (u n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih v => v :: ih (vmF (nat_lit 24) T v)) n u

@[expose] noncomputable def twoK (mem : Nat → Bool) (Q : List Nat) (u₂ : Nat) (P : List Nat) :
    Bool :=
  allL (fun w => orB (Nat.beq w u₂) (notB (allN (nat_lit 13) fun k =>
    eqBB (mem (Nat.xor w (getL (nat_lit 0) P k))) (mem (Nat.xor u₂ (getL (nat_lit 0) P k)))))) Q

@[expose] noncomputable def xorMask (V : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun v _ ih m => Nat.xor (nIf(Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 1), v, nat_lit 0))
      (ih (Nat.shiftRight m (nat_lit 1)))) V

@[expose] noncomputable def unitK (V UM : List Nat) : Bool :=
  allN (nat_lit 24) fun b => Nat.beq (xorMask V (getL (nat_lit 0) UM b)) (pw2 b)

@[expose] noncomputable def normK (CT : List Nat) : Bool :=
  allL (fun z => orB (notB (andB (eqK (powWK z (nat_lit 3)) oneK) (notB (eqK z oneK))))
    (allL (fun g => orB (notB (orB (eqK (mulWK g z) (mulWK z g))
        (eqK (mulWK g z) (mulWK (mulWK z z) g))))
      (eqK (powWK (powWK g (nat_lit 3)) (nat_lit 13)) oneK)) CT)) CT

@[expose] noncomputable def vK (I J r : Nat) : Nat :=
  nIf(Nat.beq r (nat_lit 0), oneK, nIf(Nat.beq r (nat_lit 1), I,
    nIf(Nat.beq r (nat_lit 2), J, mulWK I J)))

@[expose] noncomputable def centK (Y I J E : Nat) (CT : List Nat) : Bool :=
  andB (Nat.beq (lenL CT) (nat_lit 156)) (allN (nat_lit 156) fun t =>
    eqK (getL (nat_lit 0) CT t) (mulWK (mulWK (powWK Y (Nat.div t (nat_lit 12)))
      (vK I J (Nat.mod (Nat.div t (nat_lit 3)) (nat_lit 4)))) (powWK E (Nat.mod t (nat_lit 3)))))

@[expose] noncomputable def nodupK : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a t ih => andB (allL (fun b => notB (Nat.beq a b)) t) ih)

@[expose] noncomputable def ordK (X n : Nat) : Bool :=
  andB (eqK (powWK X n) oneK) (notB (eqK X oneK))

@[expose] noncomputable def commK (X Y : Nat) : Bool := eqK (mulWK X Y) (mulWK Y X)

@[expose] noncomputable def thirteenOK (mem : Nat → Bool) (M MI : Nat → Nat) (N : Nat)
    (ws : List (List Nat)) (ix tk : List Nat) (ts : List (Nat × Bool)) (Q : List Nat) (u₁ u₂ : Nat)
    (UM CT : List Nat) : Bool :=
  andB (dagWK M MI (nat_lit 2) N ws) (andB (Nat.beq (lenL ix) (nat_lit 4))
  (andB (allL (fun k => Nat.blt k N) ix)
  (andB (ordK (M (getL (nat_lit 0) ix (nat_lit 0))) (nat_lit 13))
  (andB (ordK (M (getL (nat_lit 0) ix (nat_lit 1))) (nat_lit 3))
  (andB (ordK (M (getL (nat_lit 0) ix (nat_lit 2))) (nat_lit 2))
  (andB (ordK (M (getL (nat_lit 0) ix (nat_lit 3))) (nat_lit 2))
  (andB (commK (M (getL (nat_lit 0) ix (nat_lit 1))) (M (getL (nat_lit 0) ix (nat_lit 0))))
  (andB (commK (M (getL (nat_lit 0) ix (nat_lit 2))) (M (getL (nat_lit 0) ix (nat_lit 0))))
  (andB (commK (M (getL (nat_lit 0) ix (nat_lit 3))) (M (getL (nat_lit 0) ix (nat_lit 0))))
  (andB (Nat.beq (lenL tk) (lenP ts))
  (andB (allN (lenL tk) fun n => Nat.beq (getP ts n) (trK (nat_lit 24)
    (powWK (M (getL (nat_lit 0) ix (nat_lit 0))) (getL (nat_lit 0) tk n))))
  (andB (Nat.beq (lenL Q) (nat_lit 156))
  (andB (Nat.blt u₁ (pw2 (nat_lit 24))) (andB (Nat.blt u₂ (pw2 (nat_lit 24)))
  (andB (memL Q u₁) (andB (memL Q u₂) (andB (tauK mem ts u₁) (andB (tauK mem ts u₂)
  (andB (twoK mem Q u₂ (orbL (trK (nat_lit 24) (M (getL (nat_lit 0) ix (nat_lit 0)))) u₁ (nat_lit 13)))
  (andB (unitK (orbL (trK (nat_lit 24) (M (getL (nat_lit 0) ix (nat_lit 0)))) u₁ (nat_lit 12) ++
      orbL (trK (nat_lit 24) (M (getL (nat_lit 0) ix (nat_lit 0)))) u₂ (nat_lit 12)) UM)
  (andB (centK (M (getL (nat_lit 0) ix (nat_lit 0))) (M (getL (nat_lit 0) ix (nat_lit 2)))
      (M (getL (nat_lit 0) ix (nat_lit 3))) (M (getL (nat_lit 0) ix (nat_lit 1))) CT)
  (andB (nodupK (CT.map fun g => vmF (nat_lit 24) (trK (nat_lit 24) g) u₁))
    (normK CT)))))))))))))))))))))))

end CFSG.KD.Co1Thirteen

end

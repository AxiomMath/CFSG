module

public import CFSG.LocalAnalysis.StandardType.GGFrameE78Defs
import Certificates.Kernel.FrameE78.Glue

public section

namespace Certificates

open CFSG.StandardType.FrameRoute CFSG.KC.FrameE78 CFSG.KC.FrameE78.Refl CFSG.KD.FrameE78

private theorem cm7 : ∀ p q : Fin 7,
    ((cij C7 p q : ℕ) : ZMod 3) = ((CartanMatrix.E 7 p q : ℤ) : ZMod 3) := by
  decide +kernel

private theorem cm8 : ∀ p q : Fin 8,
    ((cij C8 p q : ℕ) : ZMod 3) = ((CartanMatrix.E 8 p q : ℤ) : ZMod 3) := by
  decide +kernel

private theorem feS_eq {n C : ℕ}
    (h : ∀ p q : Fin n, ((cij C p q : ℕ) : ZMod 3) = ((CartanMatrix.E n p q : ℤ) : ZMod 3))
    (i : Fin n) : feS n i = sS (Cm n C) i := by
  ext p q
  rw [sS, rf, Matrix.of_apply, mulVec_ev]
  change _ = _ - ((cij C p i : ℕ) : ZMod 3) * ev i q
  rw [h p i]
  by_cases hq : q = i
  · subst hq
    simp [feS]
  · simp [feS, hq, Pi.single_apply]

private theorem der_iff {n : ℕ} {S : Fin n → FEMat n} (hS : ∀ i, feS n i = S i) (r : FEMat n) :
    FEConjDer n r ↔ ConjDer S r := by
  constructor
  · intro h
    induction h with
    | base i =>
      rw [hS]
      exact ConjDer.base i
    | conj i _ ih =>
      rw [hS]
      exact ConjDer.conj i ih
  · intro h
    induction h with
    | base i =>
      rw [← hS]
      exact FEConjDer.base i
    | conj i _ ih =>
      rw [← hS]
      exact FEConjDer.conj i ih

private theorem facts_of {n C : ℕ}
    (hcm : ∀ p q : Fin n, ((cij C p q : ℕ) : ZMod 3) = ((CartanMatrix.E n p q : ℤ) : ZMod 3))
    (hF : (∀ r t, ConjDer (sS (Cm n C)) r → ConjDer (sS (Cm n C)) t →
      r = t ∨ r * t = t * r ∨ r * t * r = t * r * t) ∧
      ∀ x : Fin n → ZMod 3, x ≠ 0 → Dich (AlwP n) (fixSet (Cm n C) x)) :
    (∀ r ∈ feT n, ∀ t ∈ feT n, r = t ∨ r * t = t * r ∨ r * t * r = t * r * t) ∧
    ∀ x : FEVec n, x ≠ 0 →
      (∃ P Q : Set (FEMat n), P ∪ Q = feTx n x ∧ Disjoint P Q ∧ P.Nonempty ∧ Q.Nonempty ∧
          (∀ r ∈ P, ∀ t ∈ P, t * r * t ∈ P) ∧ (∀ r ∈ Q, ∀ t ∈ Q, t * r * t ∈ Q) ∧
          ∀ r ∈ P, ∀ t ∈ Q, r * t = t * r) ∨
      ∃ d : ℕ, (∀ r ∈ feTx n x, Set.ncard {t | t ∈ feTx n x ∧ r * t ≠ t * r} = d) ∧
        ((n = 7 ∧ ((Set.ncard (feTx n x) = 21 ∧ d = 10) ∨ (Set.ncard (feTx n x) = 30 ∧ d = 16) ∨
            (Set.ncard (feTx n x) = 36 ∧ d = 20))) ∨
         (n = 8 ∧ ((Set.ncard (feTx n x) = 36 ∧ d = 14) ∨ (Set.ncard (feTx n x) = 42 ∧ d = 20) ∨
            (Set.ncard (feTx n x) = 63 ∧ d = 32)))) := by
  have hS := feS_eq hcm
  have hT : ∀ x, feTx n x = fixSet (Cm n C) x := fun x => by
    ext r
    exact and_congr (der_iff hS r) Iff.rfl
  refine ⟨fun r hr t ht => hF.1 r t ((der_iff hS r).1 hr) ((der_iff hS t).1 ht), fun x hx => ?_⟩
  rw [hT x]
  exact hF.2 x hx

open CFSG.StandardType.FrameRoute in
theorem certificate709548 : ∀ {n : ℕ}, (n = 7 ∨ n = 8) →
    (∀ r ∈ feT n, ∀ t ∈ feT n, r = t ∨ r * t = t * r ∨ r * t * r = t * r * t) ∧
    ∀ x : FEVec n, x ≠ 0 →
      (∃ P Q : Set (FEMat n), P ∪ Q = feTx n x ∧ Disjoint P Q ∧ P.Nonempty ∧ Q.Nonempty ∧
          (∀ r ∈ P, ∀ t ∈ P, t * r * t ∈ P) ∧ (∀ r ∈ Q, ∀ t ∈ Q, t * r * t ∈ Q) ∧
          ∀ r ∈ P, ∀ t ∈ Q, r * t = t * r) ∨
      ∃ d : ℕ, (∀ r ∈ feTx n x, Set.ncard {t | t ∈ feTx n x ∧ r * t ≠ t * r} = d) ∧
        ((n = 7 ∧ ((Set.ncard (feTx n x) = 21 ∧ d = 10) ∨ (Set.ncard (feTx n x) = 30 ∧ d = 16) ∨
            (Set.ncard (feTx n x) = 36 ∧ d = 20))) ∨
         (n = 8 ∧ ((Set.ncard (feTx n x) = 36 ∧ d = 14) ∨ (Set.ncard (feTx n x) = 42 ∧ d = 20) ∨
            (Set.ncard (feTx n x) = 63 ∧ d = 32)))) :=
  fun {n} hn => by
    rcases hn with rfl | rfl
    · exact facts_of cm7 frame7_facts
    · exact facts_of cm8 frame8_facts

end Certificates

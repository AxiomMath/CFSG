module

public import CFSG.LocalAnalysis.StandardType.GGFrameE78Defs
import Certificates.Kernel.FrameWhole.Glue

public section

namespace Certificates

open CFSG.StandardType.FrameRoute CFSG.KC.FrameE78 CFSG.KC.FrameE78.Refl CFSG.KD.FrameE78
  CFSG.KD.FrameWhole

private theorem wcm6 : ∀ p q : Fin 6,
    ((cij C6 p q : ℕ) : ZMod 3) = ((CartanMatrix.E 6 p q : ℤ) : ZMod 3) := by
  decide +kernel

private theorem wcm7 : ∀ p q : Fin 7,
    ((cij C7 p q : ℕ) : ZMod 3) = ((CartanMatrix.E 7 p q : ℤ) : ZMod 3) := by
  decide +kernel

private theorem wcm8 : ∀ p q : Fin 8,
    ((cij C8 p q : ℕ) : ZMod 3) = ((CartanMatrix.E 8 p q : ℤ) : ZMod 3) := by
  decide +kernel

private theorem wfeS_eq {n C : ℕ}
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

private theorem wfeT_eq {n C : ℕ}
    (h : ∀ p q : Fin n, ((cij C p q : ℕ) : ZMod 3) = ((CartanMatrix.E n p q : ℤ) : ZMod 3)) :
    feT n = {r | ConjDer (sS (Cm n C)) r} := by
  have hS := wfeS_eq h
  ext r
  constructor
  · intro hr
    induction hr with
    | base i =>
      rw [hS]
      exact ConjDer.base i
    | conj i _ ih =>
      rw [hS]
      exact ConjDer.conj i ih
  · intro hr
    induction hr with
    | base i =>
      rw [← hS]
      exact FEConjDer.base i
    | conj i _ ih =>
      rw [← hS]
      exact FEConjDer.conj i ih

private theorem wfacts_of {n C N d : ℕ}
    (h : ∀ p q : Fin n, ((cij C p q : ℕ) : ZMod 3) = ((CartanMatrix.E n p q : ℤ) : ZMod 3))
    (hF : WholeFacts n C N d) :
    (feT n).ncard = N ∧ (∀ r ∈ feT n, {t | t ∈ feT n ∧ r * t ≠ t * r}.ncard = d) ∧
      ∀ r ∈ feT n, ∀ t ∈ feT n,
        Relation.ReflTransGen (fun a b => a ∈ feT n ∧ b ∈ feT n ∧ a * b ≠ b * a) r t := by
  rw [wfeT_eq h]
  exact ⟨hF.1, fun r hr => hF.2.1 r hr, fun r hr t ht => hF.2.2 r t hr ht⟩

open CFSG.StandardType.FrameRoute in
theorem certificate709590 : ∀ {n N d : ℕ},
    ((n = 6 ∧ N = 36 ∧ d = 20) ∨ (n = 7 ∧ N = 63 ∧ d = 32) ∨ (n = 8 ∧ N = 120 ∧ d = 56)) →
    (feT n).ncard = N ∧ (∀ r ∈ feT n, {t | t ∈ feT n ∧ r * t ≠ t * r}.ncard = d) ∧
      ∀ r ∈ feT n, ∀ t ∈ feT n,
        Relation.ReflTransGen (fun a b => a ∈ feT n ∧ b ∈ feT n ∧ a * b ≠ b * a) r t :=
  fun {n N d} h => by
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact wfacts_of wcm6 whole6_facts
    · exact wfacts_of wcm7 whole7_facts
    · exact wfacts_of wcm8 whole8_facts

end Certificates

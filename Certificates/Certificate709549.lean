module

public import CFSG.LocalAnalysis.StandardType.GGFrameE78Defs
import Certificates.Kernel.FrameE78.RootGlue

public section

namespace Certificates

open CFSG.StandardType.FrameRoute CFSG.KC.FrameE78 CFSG.KC.FrameE78.Refl CFSG.KD.FrameE78

private theorem cm7r : ∀ p q : Fin 7,
    ((cij C7 p q : ℕ) : ZMod 3) = ((CartanMatrix.E 7 p q : ℤ) : ZMod 3) := by
  decide +kernel

private theorem feS_eq7 (i : Fin 7) : feS 7 i = sS (Cm 7 C7) i := by
  ext p q
  rw [sS, rf, Matrix.of_apply, mulVec_ev]
  change _ = _ - ((cij C7 p i : ℕ) : ZMod 3) * ev i q
  rw [cm7r p i]
  by_cases hq : q = i
  · subst hq
    simp [feS]
  · simp [feS, hq, Pi.single_apply]

private theorem der_iff7 (r : FEMat 7) : FEConjDer 7 r ↔ ConjDer (sS (Cm 7 C7)) r := by
  constructor
  · intro h
    induction h with
    | base i =>
      rw [feS_eq7]
      exact ConjDer.base i
    | conj i _ ih =>
      rw [feS_eq7]
      exact ConjDer.conj i ih
  · intro h
    induction h with
    | base i =>
      rw [← feS_eq7]
      exact FEConjDer.base i
    | conj i _ ih =>
      rw [← feS_eq7]
      exact FEConjDer.conj i ih

open CFSG.StandardType.FrameRoute in
theorem certificate709549 : ∀ {v y : FEVec 7}, ((feTx 7 v).ncard = 21 ∨ (feTx 7 v).ncard = 36) →
    13 ≤ (feTx 7 v ∩ feTx 7 y).ncard →
      ∃ c : ZMod 3, ∃ t ∈ feT 7, t.mulVec (y + c • v) = -(y + c • v) :=
  fun {v y} hv hy => by
    have hT : ∀ x, feTx 7 x = fixSet (Cm 7 C7) x := fun x => by
      ext r
      exact and_congr (der_iff7 r) Iff.rfl
    rw [hT] at hv
    rw [hT, hT] at hy
    obtain ⟨c, t, ht, e⟩ := root7_facts v hv y hy
    exact ⟨c, t, (der_iff7 t).2 ht, e⟩

end Certificates

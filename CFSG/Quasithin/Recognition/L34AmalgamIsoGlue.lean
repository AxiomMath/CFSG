module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoFactor

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem exists_glue
    {L : Type*} [Group L] {L₁ L₂ E₁ E₂ : Subgroup L}
    (ψ₁ : ↥m22TwoStab ≃* ↥L₁) (ψ₂ : ↥m22PtHexStab ≃* ↥L₂)
    (hB₁ : ∀ g : ↥m22TwoStab, ((ψ₁ g : ↥L₁) : L) ∈ L₂ ↔ (g : M22) ∈ m22PtHexStab)
    (hB₂ : ∀ g : ↥m22PtHexStab, ((ψ₂ g : ↥L₂) : L) ∈ L₁ ↔ (g : M22) ∈ m22TwoStab)
    (hE₁ : ∀ g : ↥m22TwoStab, ((ψ₁ g : ↥L₁) : L) ∈ E₁ ↔ (g : M22) ∈ barA1)
    (hE₂ : ∀ g : ↥m22TwoStab, (g : M22) ∈ m22PtHexStab →
      (((ψ₁ g : ↥L₁) : L) ∈ E₂ ↔ (g : M22) ∈ barA2))
    (hE₁' : ∀ g : ↥m22PtHexStab, ((ψ₂ g : ↥L₂) : L) ∈ E₁ ↔ (g : M22) ∈ barA1)
    (hE₂' : ∀ g : ↥m22PtHexStab, ((ψ₂ g : ↥L₂) : L) ∈ E₂ ↔ (g : M22) ∈ barA2) :
    ∃ (φ₁ : ↥m22TwoStab ≃* ↥L₁) (φ₂ : ↥m22PtHexStab ≃* ↥L₂),
      (∀ (b : M22) (h₁ : b ∈ m22TwoStab) (h₂ : b ∈ m22PtHexStab),
        ((φ₁ ⟨b, h₁⟩ : ↥L₁) : L) = φ₂ ⟨b, h₂⟩) ∧
      ∀ p : ↥m22TwoStab, ((φ₁ p : ↥L₁) : L) ∈ L₂ ↔ (p : M22) ∈ m22PtHexStab := by
  classical
  let tw : ∀ g : M22, g ∈ m22TwoStab → g ∈ m22PtHexStab → ↥m22PtHexStab :=
    fun g h₁ h₂ => ψ₂.symm ⟨_, (hB₁ ⟨g, h₁⟩).mpr h₂⟩
  have htw : ∀ (g : M22) (h₁ : g ∈ m22TwoStab) (h₂ : g ∈ m22PtHexStab),
      ((ψ₂ (tw g h₁ h₂) : ↥L₂) : L) = ((ψ₁ ⟨g, h₁⟩ : ↥L₁) : L) := by
    intro g h₁ h₂
    simp only [tw, MulEquiv.apply_symm_apply]
  have htw₁ : ∀ (g : M22) (h₁ : g ∈ m22TwoStab) (h₂ : g ∈ m22PtHexStab),
      ((tw g h₁ h₂ : ↥m22PtHexStab) : M22) ∈ m22TwoStab := by
    intro g h₁ h₂
    rw [← hB₂, htw g h₁ h₂]
    exact (ψ₁ _).2
  let θ : M22 → M22 := fun g =>
    if h : g ∈ m22TwoStab ∧ g ∈ m22PtHexStab then (tw g h.1 h.2 : M22) else 1
  have hθ : ∀ (g : M22) (h₁ : g ∈ m22TwoStab) (h₂ : g ∈ m22PtHexStab),
      θ g = (tw g h₁ h₂ : M22) := fun g h₁ h₂ =>
    dite_eq_left (show g ∈ m22TwoStab ∧ g ∈ m22PtHexStab from ⟨h₁, h₂⟩)
  have hθaut : IsAutB θ := by
    refine ⟨fun g hg => ?_, fun g hg h hh => ?_, fun g hg h hh e => ?_⟩
    · rw [hθ g hg.1 hg.2]
      exact ⟨htw₁ g hg.1 hg.2, (tw g hg.1 hg.2).2⟩
    · have hgh := barB.mul_mem hg hh
      rw [hθ _ hgh.1 hgh.2, hθ g hg.1 hg.2, hθ h hh.1 hh.2, ← Subgroup.coe_mul]
      congr 1
      apply ψ₂.injective
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, htw _ hgh.1 hgh.2, htw g hg.1 hg.2, htw h hh.1 hh.2,
        show (⟨g * h, hgh.1⟩ : ↥m22TwoStab) = ⟨g, hg.1⟩ * ⟨h, hh.1⟩ from rfl, map_mul,
        Subgroup.coe_mul]
    · rw [hθ g hg.1 hg.2, hθ h hh.1 hh.2] at e
      have e' := congrArg (fun x : ↥m22PtHexStab => ((ψ₂ x : ↥L₂) : L)) (Subtype.ext e)
      simp only [htw] at e'
      exact congrArg Subtype.val (ψ₁.injective (Subtype.ext e'))
  have hA1 : ∀ g ∈ barB, θ g ∈ barA1 ↔ g ∈ barA1 := by
    intro g hg
    rw [hθ g hg.1 hg.2, ← hE₁' (tw g hg.1 hg.2), htw g hg.1 hg.2, hE₁]
  have hA2 : ∀ g ∈ barB, θ g ∈ barA2 ↔ g ∈ barA2 := by
    intro g hg
    rw [hθ g hg.1 hg.2, ← hE₂' (tw g hg.1 hg.2), htw g hg.1 hg.2, hE₂ ⟨g, hg.1⟩ hg.2]
  obtain ⟨α₁, α₂, hα₁, -, hfac⟩ := exists_aut_factor hθaut hA1 hA2
  refine ⟨α₁.trans ψ₁, α₂.trans ψ₂, fun b h₁ h₂ => ?_, fun p => ?_⟩
  · have hc₂ : ((α₁ ⟨b, h₁⟩ : ↥m22TwoStab) : M22) ∈ m22PtHexStab := (hα₁ ⟨b, h₁⟩).mpr h₂
    have h := hfac b h₁ h₂
    rw [hθ _ (α₁ ⟨b, h₁⟩).2 hc₂] at h
    have e : tw _ (α₁ ⟨b, h₁⟩).2 hc₂ = α₂ ⟨b, h₂⟩ := Subtype.ext h
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← e, htw _ (α₁ ⟨b, h₁⟩).2 hc₂]
  · rw [MulEquiv.trans_apply, hB₁, hα₁]

end CFSG.Quasithin.L34Amalgam

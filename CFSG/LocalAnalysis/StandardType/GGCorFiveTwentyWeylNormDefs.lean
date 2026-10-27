module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenElt

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative

section NormInner

variable {G H : Type} [Group G] [Group H]

@[expose] def NormInducesInner (W : Subgroup G) : Prop :=
  ∀ φ ∈ Subgroup.normalizer (W : Set G), ∃ w ∈ W, ∀ v ∈ W, φ * v * φ⁻¹ = w * v * w⁻¹

theorem NormInducesInner.of_mulEquiv (e : G ≃* H) {W : Subgroup G} {W' : Subgroup H}
    (hW : ∀ x, x ∈ W ↔ e x ∈ W') (h : NormInducesInner W') : NormInducesInner W := by
  intro φ hφ
  have hφ' : e φ ∈ Subgroup.normalizer (W' : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← hW, ← map_inv, ← map_mul, ← map_mul, ← hW]
    exact Subgroup.mem_normalizer_iff.mp hφ x
  obtain ⟨w', hw', hw'v⟩ := h _ hφ'
  obtain ⟨w, rfl⟩ := e.surjective w'
  refine ⟨w, (hW w).mpr hw', fun v hv => e.injective ?_⟩
  have := hw'v (e v) ((hW v).mp hv)
  simpa only [map_mul, map_inv] using this

end NormInner

section Induced

variable {p : ℕ} {R : Type} [Group R]

@[expose] def ggTorusInduced {k : ℕ} (τ : Multiplicative (Fin k → ZMod p) →* R) :
    Subgroup (MulAut (Multiplicative (Fin k → ZMod p))) where
  carrier := {u | ∃ g : R, ∀ f, g * τ f * g⁻¹ = τ (u f)}
  mul_mem' := by
    rintro u₁ u₂ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    refine ⟨g₁ * g₂, fun f => ?_⟩
    calc g₁ * g₂ * τ f * (g₁ * g₂)⁻¹ = g₁ * (g₂ * τ f * g₂⁻¹) * g₁⁻¹ := by group
      _ = g₁ * τ (u₂ f) * g₁⁻¹ := by rw [h₂]
      _ = τ (u₁ (u₂ f)) := h₁ _
  one_mem' := ⟨1, fun f => by simp⟩
  inv_mem' := by
    rintro u ⟨g, h⟩
    refine ⟨g⁻¹, fun f => ?_⟩
    have h1 := h (u⁻¹ f)
    rw [MulAut.apply_inv_self] at h1
    calc g⁻¹ * τ f * g⁻¹⁻¹ = g⁻¹ * (g * τ (u⁻¹ f) * g⁻¹) * g := by rw [h1]; group
      _ = τ (u⁻¹ f) := by group

theorem mem_ggTorusInduced {k : ℕ} {τ : Multiplicative (Fin k → ZMod p) →* R}
    {u : MulAut (Multiplicative (Fin k → ZMod p))} :
    u ∈ ggTorusInduced τ ↔ ∃ g : R, ∀ f, g * τ f * g⁻¹ = τ (u f) :=
  Iff.rfl

theorem ggTorusInduced_comp_mulEquiv {R' : Type} [Group R'] {k : ℕ} (e : R ≃* R')
    (τ : Multiplicative (Fin k → ZMod p) →* R) :
    ggTorusInduced (e.toMonoidHom.comp τ) = ggTorusInduced τ := by
  ext u
  rw [mem_ggTorusInduced, mem_ggTorusInduced]
  constructor
  · rintro ⟨g', hg'⟩
    refine ⟨e.symm g', fun f => e.injective ?_⟩
    have h1 := hg' f
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h1
  · rintro ⟨g, hg⟩
    refine ⟨e g, fun f => ?_⟩
    have h1 := congrArg e (hg f)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv] using h1

end Induced

end CFSG.StandardType

end

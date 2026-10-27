module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative

@[expose] def ggTorusInducedReflSet (p : ℕ) {R : Type} [Group R] {k : ℕ}
    (τ : Multiplicative (Fin k → ZMod p) →* R) :
    Set (MulAut (Multiplicative (Fin k → ZMod p))) :=
  {s | s ^ (p - 1) = 1 ∧
    Nat.card {f : Multiplicative (Fin k → ZMod p) // s f = f} * p =
      Nat.card (Multiplicative (Fin k → ZMod p)) ∧
    ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (s f)}

@[expose] def GGTorusWeylGenElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∃ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R), Function.Injective τ ∧
      τ.range = E ∧
      (∀ (L' : Type) [Group L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' →
          ∃ σ : Multiplicative (Fin k → ZMod p) →* L', ψ.comp σ = τ) ∧
      ∀ g : R, g ∈ Subgroup.normalizer (E : Set R) →
        ∃ u ∈ Subgroup.closure (ggTorusInducedReflSet p τ), ∀ f, g * τ f * g⁻¹ = τ (u f)

section Transfer

variable {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusWeylGenElt_of_mulEquiv {R' : Type} [Group R'] (e : R ≃* R')
    (h : GGTorusWeylGenElt p r R') : GGTorusWeylGenElt p r R := by
  intro E hE hr h3
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hmem : ∀ x : R, e x ∈ E.map e.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  obtain ⟨k, τ, hτinj, hτE, hsec, hnorm⟩ :=
    h (E.map e.toMonoidHom) (isElemAbelian_map hE _) (hcard ▸ hr) (hcard ▸ h3)
  have hsub : ggTorusInducedReflSet p τ ⊆
      ggTorusInducedReflSet p (e.symm.toMonoidHom.comp τ) := by
    intro s hs
    obtain ⟨hs1, hs2, w, hw⟩ := hs
    refine ⟨hs1, hs2, e.symm w, fun f => ?_⟩
    have h1 : e.symm (w * τ f * w⁻¹) = e.symm (τ (s f)) := congrArg e.symm (hw f)
    simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h1
  refine ⟨k, e.symm.toMonoidHom.comp τ, e.symm.injective.comp hτinj, ?_, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      have : τ f ∈ τ.range := ⟨f, rfl⟩
      rw [hτE] at this
      rw [← hmem]
      simpa using this
    · intro hx
      have : e x ∈ τ.range := hτE ▸ (hmem x).mpr hx
      obtain ⟨f, hf⟩ := this
      exact ⟨f, by simp [hf]⟩
  · intro L' _ ψ hψ hker
    obtain ⟨σ, hσ⟩ := hsec L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ)
      (fun l hl => hker (by simpa [MonoidHom.mem_ker] using hl))
    refine ⟨σ, MonoidHom.ext fun f => ?_⟩
    have h1 := DFunLike.congr_fun hσ f
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1 ⊢
    rw [← h1, MulEquiv.symm_apply_apply]
  · intro g hg
    have hg' : e g ∈ Subgroup.normalizer (E.map e.toMonoidHom : Set R') := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [← map_inv, ← map_mul, ← map_mul]
      exact (hmem y).trans ((Subgroup.mem_set_normalizer_iff.mp hg y).trans
        (hmem (g * y * g⁻¹)).symm)
    obtain ⟨u, hu, hconj'⟩ := hnorm (e g) hg'
    refine ⟨u, Subgroup.closure_mono hsub hu, fun f => ?_⟩
    have h1 : e.symm (e g * τ f * (e g)⁻¹) = e.symm (τ (u f)) := congrArg e.symm (hconj' f)
    simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h1

end Transfer

end CFSG.StandardType

end

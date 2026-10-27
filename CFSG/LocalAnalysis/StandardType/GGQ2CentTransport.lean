module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentralizerPort

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

theorem range_ggBeta_eq_map {G : Type} [Group G] {L Bs : Subgroup G} {R₁ R₂ : Type} [Group R₁]
    [Group R₂] (θ₁ : L ⧸ Subgroup.center L ≃* R₁) (θ₂ : L ⧸ Subgroup.center L ≃* R₂)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    (ggBeta L θ₂ hN).range =
      (ggBeta L θ₁ hN).range.map (MulAut.congr (θ₁.symm.trans θ₂)).toMonoidHom := by
  have key : ∀ b : Bs, ggBeta L θ₂ hN b =
      MulAut.congr (θ₁.symm.trans θ₂) (ggBeta L θ₁ hN b) := by
    intro b
    rw [ggBeta_eq L θ₂ hN b, ggBeta_eq L θ₁ hN b]
    ext r
    simp [ggLAut, MulAut.congr_apply]
  ext φ
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨ggBeta L θ₁ hN b, ⟨b, rfl⟩, (key b).symm⟩
  · intro hφ
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hψ
    exact ⟨b, key b⟩

theorem internalAt_of_mulEquiv {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {hS : GGQTwoSetting p B Bs x L D J} {R₁ R₂ : Type} [Group R₁]
    [Group R₂] (θ₁ : L ⧸ Subgroup.center L ≃* R₁) (θ₂ : L ⧸ Subgroup.center L ≃* R₂)
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)} (h : internalAt p B Bs x L D J hS R₁ θ₁ hN) :
    internalAt p B Bs x L D J hS R₂ θ₂ hN := by
  unfold internalAt at h ⊢
  obtain ⟨U, hUe, hUB, hUmap, hUz⟩ := h
  let q := QuotientGroup.mk' (Subgroup.center L)
  let e : R₁ ≃* R₂ := θ₁.symm.trans θ₂
  let f : MulAut R₁ →* MulAut R₂ := (MulAut.congr e).toMonoidHom
  let g₁ : L →* MulAut R₁ :=
    (MulAut.conj : R₁ →* MulAut R₁).comp (θ₁.toMonoidHom.comp q)
  let g₂ : L →* MulAut R₂ :=
    (MulAut.conj : R₂ →* MulAut R₂).comp (θ₂.toMonoidHom.comp q)
  have hf : f = (MulAut.congr (θ₁.symm.trans θ₂)).toMonoidHom := rfl
  have hUmap' : U.map g₁ =
      (ggBeta L θ₁ hN).range ⊓ (MulAut.conj : R₁ →* MulAut R₁).range := by
    simpa [g₁, q] using hUmap
  have hg : g₂ = f.comp g₁ := by
    ext l r
    simp [g₂, g₁, f, e, MulAut.congr_apply]
  have hconj : (MulAut.conj : R₁ →* MulAut R₁).range.map f =
      (MulAut.conj : R₂ →* MulAut R₂).range := by
    ext φ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hψ
      exact ⟨e a, by
        ext z
        simp [f, MulAut.congr_apply]⟩
    · rintro ⟨b, rfl⟩
      refine ⟨MulAut.conj (e.symm b), ⟨e.symm b, rfl⟩, ?_⟩
      ext z
      simp [f, MulAut.congr_apply]
  have hmap : U.map g₂ =
      (ggBeta L θ₂ hN).range ⊓ (MulAut.conj : R₂ →* MulAut R₂).range := by
    calc
      U.map g₂ = U.map (f.comp g₁) := by rw [hg]
      _ = (U.map g₁).map f := by rw [Subgroup.map_map]
      _ = ((ggBeta L θ₁ hN).range ⊓
            (MulAut.conj : R₁ →* MulAut R₁).range).map f := by
        rw [hUmap']
      _ = (ggBeta L θ₁ hN).range.map f ⊓
            (MulAut.conj : R₁ →* MulAut R₁).range.map f := by
        rw [Subgroup.map_inf (ggBeta L θ₁ hN).range
          (MulAut.conj : R₁ →* MulAut R₁).range f (MulAut.congr e).injective]
      _ = (ggBeta L θ₂ hN).range ⊓ (MulAut.conj : R₂ →* MulAut R₂).range := by
        rw [hconj, hf, ← range_ggBeta_eq_map θ₁ θ₂ hN]
  exact ⟨U, hUe, hUB, hmap, hUz⟩

theorem labelTUInput_of_exists (S : LargeEvenLabel → Prop)
    (h : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (hS : GGQTwoSetting p B Bs x L D J), labelOn S p Bs L →
      ∃ (R : Type) (_ : Group R) (θ : L ⧸ Subgroup.center L ≃* R),
        ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
          toralAt p B Bs x L D J hS R θ hN ∧ (x ∈ L → internalAt p B Bs x L D J hS R θ hN)) :
    labelTUInput S := by
  unfold labelTUInput
  intro G hG hGfin p B Bs x L D J hS hlabel R hR θ hN
  obtain ⟨R₀, hR₀, θ₀, hθ₀⟩ := h G p B Bs x L D J hS hlabel
  let hR₀inst := hR₀
  refine ⟨actionThree_ggBeta_congr θ θ₀ hN (hθ₀ hN).1, ?_⟩
  intro hx
  exact internalAt_of_mulEquiv θ₀ θ ((hθ₀ hN).2 hx)

end CFSG.StandardType.GGQ2CentPort

end

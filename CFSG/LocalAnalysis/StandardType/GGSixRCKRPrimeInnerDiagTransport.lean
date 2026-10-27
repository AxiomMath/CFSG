module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem CFSG.LieType.Universal

section

variable {U' U X : Type*} [Group U'] [Group U] [Group X]

private theorem mem_map_conj_iff' (H : Subgroup U) (w y : U) :
    y ∈ H.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * y * w ∈ H := by
  rw [Subgroup.mem_map_equiv]
  rfl

private theorem conj_mem_normalizer (e : U' ≃* U) {H' : Subgroup U'} {H : Subgroup U} {w : U}
    {h : U'} (hH : H'.map e.toMonoidHom = H.map (MulAut.conj w).toMonoidHom)
    (hh : h ∈ Subgroup.normalizer (H' : Set U')) :
    w⁻¹ * e h * w ∈ Subgroup.normalizer (H : Set U) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ y : U, y ∈ H ↔ w * y * w⁻¹ ∈ H'.map e.toMonoidHom := by
    intro y
    rw [hH, mem_map_conj_iff', show w⁻¹ * (w * y * w⁻¹) * w = y by group]
  have hnorm : ∀ q : U', q ∈ H' ↔ h * q * h⁻¹ ∈ H' := Subgroup.mem_normalizer_iff.mp hh
  have hmap : ∀ p : U, p ∈ H'.map e.toMonoidHom ↔ e h * p * (e h)⁻¹ ∈ H'.map e.toMonoidHom := by
    intro p
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have := hnorm (e.symm p)
    simpa [map_mul] using this
  have hx : w * (w⁻¹ * e h * w * x * (w⁻¹ * e h * w)⁻¹) * w⁻¹ =
      e h * (w * x * w⁻¹) * (e h)⁻¹ := by group
  rw [key x, key (w⁻¹ * e h * w * x * (w⁻¹ * e h * w)⁻¹), hx]
  exact hmap _

theorem ggPsiInnerDiag_comp_symm_of_opposite_pair
    {Δ' : UniversalRootDatum U'} {Δ : UniversalRootDatum U} (e : U' ≃* U)
    {β' : Fin Δ'.rank → ℤ} {γ : Fin Δ.rank → ℤ} {w : U}
    (hβ' : β' ∈ Δ'.roots) (hβ'n : -β' ∈ Δ'.roots)
    (hroots : ∀ δ ∈ Δ.roots, δ = γ ∨ δ = -γ)
    (h1 : (Δ'.rootGroup β').map e.toMonoidHom = (Δ.rootGroup γ).map (MulAut.conj w).toMonoidHom)
    (h2 : (Δ'.rootGroup (-β')).map e.toMonoidHom =
      (Δ.rootGroup (-γ)).map (MulAut.conj w).toMonoidHom)
    (φ : U' →* X) {b : X} (hbK : ∀ k ∈ φ.range, b⁻¹ * k * b ∈ φ.range)
    (hb : GGPsiInnerDiag Δ' φ b) :
    GGPsiInnerDiag Δ (φ.comp e.symm.toMonoidHom) b := by
  obtain ⟨g₀, hg₀, hdiag⟩ := hb
  obtain ⟨u, hu⟩ : ∃ u : U', u = e.symm w := ⟨_, rfl⟩
  obtain ⟨g₁, hg₁def⟩ : ∃ g₁ : X, g₁ = b⁻¹ * (φ u)⁻¹ * b * g₀ * φ u := ⟨_, rfl⟩
  have hg₁ : g₁ ∈ (φ.comp e.symm.toMonoidHom).range := by
    have h3 : b⁻¹ * (φ u)⁻¹ * b ∈ φ.range :=
      hbK _ (Subgroup.inv_mem _ (MonoidHom.mem_range.mpr ⟨u, rfl⟩))
    have hmem : g₁ ∈ φ.range := by
      rw [hg₁def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h3 hg₀) (MonoidHom.mem_range.mpr ⟨u, rfl⟩)
    obtain ⟨y, hy⟩ := hmem
    exact ⟨e y, by simp [hy]⟩
  have hbg : b * g₁ = (φ u)⁻¹ * (b * g₀) * φ u := by rw [hg₁def]; group
  have htor : ∀ h' ∈ ggTorus Δ', w⁻¹ * e h' * w ∈ ggTorus Δ := by
    intro h' hh'
    simp only [ggTorus, Subgroup.mem_iInf] at hh' ⊢
    intro δ hδ
    rcases hroots δ hδ with hδ' | hδ'
    · rw [hδ']
      exact conj_mem_normalizer e h1 (hh' β' hβ')
    · rw [hδ']
      exact conj_mem_normalizer e h2 (hh' (-β') hβ'n)
  have step : ∀ (β : Fin Δ'.rank → ℤ) (γ' : Fin Δ.rank → ℤ), β ∈ Δ'.roots →
      (Δ'.rootGroup β).map e.toMonoidHom = (Δ.rootGroup γ').map (MulAut.conj w).toMonoidHom →
      ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup γ',
        (b * g₁)⁻¹ * (φ.comp e.symm.toMonoidHom) z * (b * g₁) =
          (φ.comp e.symm.toMonoidHom) (h * z * h⁻¹) := by
    intro β γ' hβ hβe
    obtain ⟨h', hh'tor, hh'⟩ := hdiag β hβ
    refine ⟨w⁻¹ * e h' * w, htor h' hh'tor, fun z hz => ?_⟩
    have hz' : w * z * w⁻¹ ∈ (Δ'.rootGroup β).map e.toMonoidHom := by
      rw [hβe, mem_map_conj_iff', show w⁻¹ * (w * z * w⁻¹) * w = z by group]
      exact hz
    obtain ⟨z', hz'mem, hz'eq⟩ := Subgroup.mem_map.mp hz'
    have hzeq : e.symm z = u⁻¹ * z' * u := by
      have h4 : z = w⁻¹ * e z' * w := by
        have h5 : (e.toMonoidHom z') = e z' := rfl
        rw [h5] at hz'eq
        rw [hz'eq]
        group
      rw [h4, hu]
      simp [map_mul, map_inv]
    have hhz : e.symm (w⁻¹ * e h' * w * z * (w⁻¹ * e h' * w)⁻¹) =
        u⁻¹ * (h' * z' * h'⁻¹) * u := by
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hzeq, hu]
      simp only [MulEquiv.symm_apply_apply, map_inv]
      group
    have hψ : ∀ y : U, (φ.comp e.symm.toMonoidHom) y = φ (e.symm y) := fun y => rfl
    rw [hψ z, hψ _, hhz, hzeq, hbg]
    have h6 := hh' z' hz'mem
    calc ((φ u)⁻¹ * (b * g₀) * φ u)⁻¹ * φ (u⁻¹ * z' * u) * ((φ u)⁻¹ * (b * g₀) * φ u)
        = (φ u)⁻¹ * ((b * g₀)⁻¹ * φ z' * (b * g₀)) * φ u := by
          simp only [map_mul, map_inv]
          group
      _ = (φ u)⁻¹ * φ (h' * z' * h'⁻¹) * φ u := by rw [h6]
      _ = φ (u⁻¹ * (h' * z' * h'⁻¹) * u) := by simp only [map_mul, map_inv]
  refine ⟨g₁, hg₁, fun δ hδ => ?_⟩
  rcases hroots δ hδ with hδ' | hδ'
  · rw [hδ']
    exact step β' γ hβ' h1
  · rw [hδ']
    exact step (-β') (-γ) hβ'n h2

end

end CFSG.StandardType

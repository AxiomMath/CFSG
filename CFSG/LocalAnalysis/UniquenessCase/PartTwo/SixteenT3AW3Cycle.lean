module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Hyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {T : Type} [CommGroup T] [Finite T] {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
  {X : Subgroup (MulAut T)}

theorem s16t_w3_cycle (h : S16tW3Hyp Y X) {f : MulAut T} (hfX : f ∈ X) (hf3 : f ^ 3 = 1)
    (hfm : ∃ i, (Y i).map f.toMonoidHom ≠ Y i) (i : ι) :
    ∃ i₁ i₂ : ι, (Y i).map f.toMonoidHom = Y i₁ ∧ (Y i₁).map f.toMonoidHom = Y i₂ ∧
      (Y i₂).map f.toMonoidHom = Y i ∧ i ≠ i₁ ∧ i ≠ i₂ ∧ i₁ ≠ i₂ ∧
      ∀ j, j = i ∨ j = i₁ ∨ j = i₂ := by
  classical
  obtain ⟨ρ, hρ⟩ := s16t_a_exists_perm_hom h.injective h.perm
  set σ := ρ ⟨f, hfX⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨f, hfX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hf3)
    rw [hσ, ← map_pow, h1, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    obtain ⟨i₀, hi₀⟩ := hfm
    apply hi₀
    rw [hρ ⟨f, hfX⟩ i₀, ← hσ, h1]
    rfl
  let e : ι ≃ Fin 3 := Fintype.equivFinOfCardEq h.card_index
  have key : ∀ τ : Equiv.Perm (Fin 3), τ ^ 3 = 1 → τ ≠ 1 → ∀ a, a ≠ τ a ∧ a ≠ τ (τ a) ∧
      τ a ≠ τ (τ a) ∧ ∀ b, b = a ∨ b = τ a ∨ b = τ (τ a) := by
    decide
  have hτ3 : e.permCongr σ ^ 3 = 1 := by
    rw [← Equiv.permCongrHom_coe, ← map_pow, hσ3, map_one]
  have hτ1 : e.permCongr σ ≠ 1 := by
    rw [← Equiv.permCongrHom_coe, Ne, MulEquiv.map_eq_one_iff]
    exact hσ1
  have hτe : ∀ a, e.permCongr σ (e a) = e (σ a) := fun a => by
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  obtain ⟨h1, h2, h3, h4⟩ := key _ hτ3 hτ1 (e i)
  simp only [hτe] at h1 h2 h3 h4
  have hσσσ : σ (σ (σ i)) = i := by
    rw [show σ (σ (σ i)) = (σ ^ 3) i by rw [pow_three]; rfl, hσ3]
    rfl
  refine ⟨σ i, σ (σ i), hρ ⟨f, hfX⟩ i, hρ ⟨f, hfX⟩ (σ i),
    (hρ ⟨f, hfX⟩ (σ (σ i))).trans (congrArg Y hσσσ),
    fun hi => h1 (congrArg e hi), fun hi => h2 (congrArg e hi), fun hi => h3 (congrArg e hi),
    fun j => ?_⟩
  rcases h4 (e j) with hj | hj | hj
  · exact Or.inl (e.injective hj)
  · exact Or.inr (Or.inl (e.injective hj))
  · exact Or.inr (Or.inr (e.injective hj))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Timmesfeld.Transvection.ModelPoints

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM

namespace ModelRank

theorem exists_perp_spForm_ne_zero {n : ℕ} {F : Type} [Field F] {a w : Fin n ⊕ Fin n → F}
    (hwa : ∀ c : F, w ≠ c • a) : ∃ z, spForm a z = 0 ∧ spForm w z ≠ 0 := by
  by_contra h
  obtain ⟨l, hl⟩ := exists_eq_smul_of_spForm_imp (v := a) (w := w) fun z hz => by
    by_contra hne
    exact h ⟨z, hz, hne⟩
  exact hwa l hl

theorem exists_perp_spForm_ne_zero_both {n : ℕ} {F : Type} [Field F] {a w w' : Fin n ⊕ Fin n → F}
    (hwa : ∀ c : F, w ≠ c • a) (hwa' : ∀ c : F, w' ≠ c • a) :
    ∃ z, spForm a z = 0 ∧ spForm w z ≠ 0 ∧ spForm w' z ≠ 0 := by
  obtain ⟨y, hay, hy⟩ := exists_perp_spForm_ne_zero hwa
  obtain ⟨z, haz, hz⟩ := exists_perp_spForm_ne_zero hwa'
  by_cases h1 : spForm w' y = 0
  · by_cases h2 : spForm w z = 0
    · refine ⟨y + z, by rw [spForm_add_right, hay, haz, add_zero], ?_, ?_⟩
      · rw [spForm_add_right, h2, add_zero]
        exact hy
      · rw [spForm_add_right, h1, zero_add]
        exact hz
    · exact ⟨z, haz, h2, hz⟩
  · exact ⟨y, hay, hy, h1⟩

theorem exists_spForm_ne_zero_both {n : ℕ} {F : Type} [Field F] {a u : Fin n ⊕ Fin n → F}
    (ha : a ≠ 0) (hu : u ≠ 0) : ∃ v, spForm a v ≠ 0 ∧ spForm u v ≠ 0 := by
  obtain ⟨v, -, hav, huv⟩ := exists_perp_spForm_ne_zero_both (a := 0) (w := a) (w' := u)
    (fun c h => ha (h.trans (smul_zero c))) (fun c h => hu (h.trans (smul_zero c)))
  exact ⟨v, hav, huv⟩

theorem exists_spForm_separate {n : ℕ} {F : Type} [Field F] {a u u' : Fin n ⊕ Fin n → F}
    (ha : a ≠ 0) (hua : ∀ c : F, u ≠ c • a) (hu' : ∀ c : F, u' ≠ c • u) :
    ∃ z, spForm a z ≠ 0 ∧ spForm u z = 0 ∧ spForm u' z ≠ 0 := by
  have hau : ∀ c : F, a ≠ c • u := by
    rintro c rfl
    have hc : c ≠ 0 := by
      rintro rfl
      exact ha (zero_smul F u)
    exact hua c⁻¹ (by rw [smul_smul, inv_mul_cancel₀ hc, one_smul])
  obtain ⟨z, huz, haz, hu'z⟩ := exists_perp_spForm_ne_zero_both hau hu'
  exact ⟨z, haz, huz, hu'z⟩

theorem exists_mat_mulVec_eq_mod {n : ℕ} {F : Type} [Field F] {a w w' : Fin n ⊕ Fin n → F}
    (hw : spForm a w = 0) (hw' : spForm a w' = 0) (hwa : ∀ c : F, w ≠ c • a)
    (hwa' : ∀ c : F, w' ≠ c • a) :
    ∃ g : StatedSp n F, SpExtras.mat n F g *ᵥ a = a ∧
      ∃ c : F, SpExtras.mat n F g *ᵥ w = w' + c • a := by
  have step : ∀ {x y : Fin n ⊕ Fin n → F}, spForm a x = 0 → spForm a y = 0 → spForm x y ≠ 0 →
      ∃ g : StatedSp n F, SpExtras.mat n F g *ᵥ a = a ∧ SpExtras.mat n F g *ᵥ x = y := by
    intro x y hx hy hxy
    have hyx : spForm y x ≠ 0 := by rw [spForm_comm]; exact neg_ne_zero.2 hxy
    obtain ⟨g, hg⟩ := exists_mat_eq_spTrans (y - x) (spForm y x)⁻¹
    refine ⟨g, ?_, ?_⟩
    · rw [hg, spTrans_mulVec, spForm_sub_left, spForm_eq_zero_comm hx, spForm_eq_zero_comm hy,
        sub_zero, mul_zero, zero_smul, add_zero]
    · rw [hg, spTrans_mulVec, spForm_sub_left, spForm_self, sub_zero, inv_mul_cancel₀ hyx,
        one_smul, add_sub_cancel]
  obtain ⟨z, haz, hwz, hw'z⟩ := exists_perp_spForm_ne_zero_both hwa hwa'
  obtain ⟨g₁, hg₁a, hg₁w⟩ := step hw haz hwz
  obtain ⟨g₂, hg₂a, hg₂z⟩ := step haz hw' (by rw [spForm_comm]; exact neg_ne_zero.2 hw'z)
  refine ⟨g₂ * g₁, ?_, 0, ?_⟩
  · rw [map_mul, ← mulVec_mulVec, hg₁a, hg₂a]
  · rw [map_mul, ← mulVec_mulVec, hg₁w, hg₂z, zero_smul, add_zero]

end ModelRank

end CFSG.Timmesfeld.Transvection

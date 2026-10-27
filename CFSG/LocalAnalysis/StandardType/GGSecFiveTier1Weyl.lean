module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.Timmesfeld.RankTwo.LevisSpin

public section

namespace CFSG.StandardType

open CFSG.Timmesfeld

theorem coxeterMatrix_reindex_apply_equiv {ι κ : Type} (M : CoxeterMatrix ι) (e : ι ≃ κ)
    (i j : ι) : (M.reindex e).M (e i) (e j) = M.M i j := by
  rw [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem coxeterMatrixA_eq_two (n : ℕ) (i j : Fin n) (h : (i : ℕ) + 1 < j) :
    (CoxeterMatrix.A n).M i j = 2 := by
  have hij : i ≠ j := by rintro rfl; omega
  have hne : ¬ ((j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)) := by
    rintro (hji | hij')
    · omega
    · omega
  simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij, if_neg hne]

theorem coxeterMatrixA_eq_three (n : ℕ) (i j : Fin n) (h : (j : ℕ) = i + 1) :
    (CoxeterMatrix.A n).M i j = 3 := by
  have hij : i ≠ j := by rintro rfl; omega
  have hne : ((j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)) := Or.inr h.symm
  simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij, if_pos hne]

private theorem edgeD_ne {n : ℕ} {i j : Fin n} (h : edgeD n i j) : i ≠ j := by
  rintro rfl
  rcases h with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega

private theorem cartanD_eq_zero_of_not_edgeD {n : ℕ} (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (h1 : ¬ edgeD n i j) (h2 : ¬ edgeD n j i) : CartanMatrix.D n i j = 0 := by
  simp only [edgeD] at h1 h2
  simp only [CartanMatrix.D, Matrix.of_apply, if_neg hij, if_neg (by omega : ¬ n ≤ 2)]
  rw [if_neg (show ¬ ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n) from by
        rintro ⟨hij1, hlt⟩
        exact h1 (Or.inl ⟨hij1, by omega⟩)),
      if_neg (show ¬ ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < n) from by
        rintro ⟨hji1, hlt⟩
        exact h2 (Or.inl ⟨hji1, by omega⟩)),
      if_neg (show ¬ ((i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n)) from by
        rintro ⟨hi3, hj2 | hj1⟩
        · exact h1 (Or.inl ⟨by omega, by omega⟩)
        · exact h1 (Or.inr ⟨hi3, hj1⟩)),
      if_neg (show ¬ ((j : ℕ) + 3 = n ∧ ((i : ℕ) + 2 = n ∨ (i : ℕ) + 1 = n)) from by
        rintro ⟨hj3, hi2 | hi1⟩
        · exact h2 (Or.inl ⟨by omega, by omega⟩)
        · exact h2 (Or.inr ⟨hj3, hi1⟩))]

private theorem cartanD_ne_zero_of_edgeD {n : ℕ} (hn : 4 ≤ n) {i j : Fin n}
    (h : edgeD n i j) : CartanMatrix.D n i j ≠ 0 := by
  have hij : i ≠ j := edgeD_ne h
  simp only [CartanMatrix.D, Matrix.of_apply]
  rw [if_neg hij, if_neg (by omega : ¬ n ≤ 2)]
  rcases h with ⟨hi1, hjlt⟩ | ⟨hi3, hj1⟩
  · by_cases hlt2 : (j : ℕ) + 2 < n
    · rw [if_pos (show (i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n from ⟨hi1, hlt2⟩)]
      omega
    · have hj2 : (j : ℕ) + 2 = n := by omega
      rw [if_neg (show ¬ ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n) from by omega),
        if_neg (show ¬ ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < n) from by omega),
        if_pos (show (i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n) from
          ⟨by omega, Or.inl hj2⟩)]
      omega
  · rw [if_neg (show ¬ ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n) from by omega),
        if_neg (show ¬ ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < n) from by omega),
        if_pos (show (i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n) from
          ⟨hi3, Or.inr hj1⟩)]
    omega

theorem ggCoxeterMatrixD_eq_two {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) (hij : i ≠ j)
    (h1 : ¬ edgeD n i j) (h2 : ¬ edgeD n j i) : ggCoxeterMatrixD n i j = 2 := by
  rw [ggCoxeterMatrixD_apply, if_neg hij,
    if_pos (cartanD_eq_zero_of_not_edgeD hn hij h1 h2)]

theorem ggCoxeterMatrixD_eq_three {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) (h : edgeD n i j) :
    ggCoxeterMatrixD n i j = 3 := by
  rw [ggCoxeterMatrixD_apply, if_neg (edgeD_ne h),
    if_neg (cartanD_ne_zero_of_edgeD hn h)]

theorem GGIsWeylMatrixAD.isWeylMatrix {ι : Type} {M : CoxeterMatrix ι}
    (h : GGIsWeylMatrixAD M) : GGIsWeylMatrix M := by
  rcases h with ⟨n, e, hn, rfl⟩ | ⟨n, e, hn, rfl⟩
  · exact Or.inl ⟨n, e, by omega, Or.inl rfl⟩
  · exact Or.inl ⟨n, e, by omega, Or.inr (Or.inr ⟨hn, rfl⟩)⟩

theorem GGIsWeylMatrixAD.le_three {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrixAD M)
    (i j : ι) (hij : i ≠ j) : M.M i j ≤ 3 := by
  rcases h with ⟨n, e, hn, rfl⟩ | ⟨n, e, hn, rfl⟩
  · rw [CoxeterMatrix.reindex_apply]
    simp only [CoxeterMatrix.A, Matrix.of_apply]
    split_ifs <;> omega
  · rw [CoxeterMatrix.reindex_apply, ggCoxeterMatrixD_apply]
    split_ifs <;> omega

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGForkNullPos

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma eq_of_row_neg_one {m : ℕ} {i k j : Fin (m + 5)}
    (hrow : ∀ j, j ≠ i → CartanMatrix.D (m + 5) i j = if j = k then -1 else 0)
    (hj : j ≠ i) (hD : CartanMatrix.D (m + 5) i j = -1) : j = k := by
  have h := hrow j hj
  rw [hD] at h
  by_contra hjk
  rw [if_neg hjk] at h
  omega

theorem cartanMatrix_D_natAdd (m : ℕ) {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    CartanMatrix.D (m + n) (Fin.natAdd m i) (Fin.natAdd m j) = CartanMatrix.D n i j := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_natAdd]
  split_ifs <;> omega

theorem ggLeafPos_D (m : ℕ) {i k : Fin (m + 5)}
    (h : GGLeafPos (CartanMatrix.D (m + 5)) i k) :
    (i.val = 0 ∧ k.val = 1) ∨ ((i.val = m + 3 ∨ i.val = m + 4) ∧ k.val = m + 2) := by
  obtain ⟨_, hrow, _⟩ := h
  have hilt : i.val < m + 5 := i.isLt
  by_cases h0 : i.val = 0
  · left
    refine ⟨h0, ?_⟩
    have hj : (⟨1, by omega⟩ : Fin (m + 5)) ≠ i := by
      intro hji
      have := congrArg Fin.val hji
      simp only [Fin.val_mk] at this
      omega
    have hD : CartanMatrix.D (m + 5) i (⟨1, by omega⟩ : Fin (m + 5)) = -1 := by
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> (try simp only [true_or, or_true, true_and, and_true,
        not_true_eq_false, not_false_eq_true] at *) <;> omega
    have hk := eq_of_row_neg_one hrow hj hD
    rw [← hk]
  · by_cases hm2 : i.val = m + 2
    · exfalso
      have hj1 : (⟨m + 1, by omega⟩ : Fin (m + 5)) ≠ i := by
        intro hji
        have := congrArg Fin.val hji
        simp only [Fin.val_mk] at this
        omega
      have hD1 : CartanMatrix.D (m + 5) i (⟨m + 1, by omega⟩ : Fin (m + 5)) = -1 := by
        simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
        split_ifs <;> (try simp only [true_or, or_true, true_and, and_true,
          not_true_eq_false, not_false_eq_true] at *) <;> omega
      have hj2 : (⟨m + 3, by omega⟩ : Fin (m + 5)) ≠ i := by
        intro hji
        have := congrArg Fin.val hji
        simp only [Fin.val_mk] at this
        omega
      have hD2 : CartanMatrix.D (m + 5) i (⟨m + 3, by omega⟩ : Fin (m + 5)) = -1 := by
        simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
        split_ifs <;> (try simp only [true_or, or_true, true_and, and_true,
          not_true_eq_false, not_false_eq_true] at *) <;> omega
      have h1 := eq_of_row_neg_one hrow hj1 hD1
      have h2 := eq_of_row_neg_one hrow hj2 hD2
      have hval := congrArg Fin.val (h1.trans h2.symm)
      simp only [Fin.val_mk] at hval
      omega
    · by_cases hm3 : i.val = m + 3
      · right
        refine ⟨Or.inl hm3, ?_⟩
        have hj : (⟨m + 2, by omega⟩ : Fin (m + 5)) ≠ i := by
          intro hji
          have := congrArg Fin.val hji
          simp only [Fin.val_mk] at this
          omega
        have hD : CartanMatrix.D (m + 5) i (⟨m + 2, by omega⟩ : Fin (m + 5)) = -1 := by
          simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
          split_ifs <;> (try simp only [true_or, or_true, true_and, and_true,
            not_true_eq_false, not_false_eq_true] at *) <;> omega
        have hk := eq_of_row_neg_one hrow hj hD
        rw [← hk]
      · by_cases hm4 : i.val = m + 4
        · right
          refine ⟨Or.inr hm4, ?_⟩
          have hj : (⟨m + 2, by omega⟩ : Fin (m + 5)) ≠ i := by
            intro hji
            have := congrArg Fin.val hji
            simp only [Fin.val_mk] at this
            omega
          have hD : CartanMatrix.D (m + 5) i (⟨m + 2, by omega⟩ : Fin (m + 5)) = -1 := by
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
            split_ifs <;> (try simp only [true_or, or_true, true_and, and_true,
              not_true_eq_false, not_false_eq_true] at *) <;> omega
          have hk := eq_of_row_neg_one hrow hj hD
          rw [← hk]
        · exfalso
          have hge : 1 ≤ i.val := by omega
          have hle : i.val ≤ m + 1 := by omega
          have hj1 : (⟨i.val - 1, by omega⟩ : Fin (m + 5)) ≠ i := by
            intro hji
            have := congrArg Fin.val hji
            simp only [Fin.val_mk] at this
            omega
          have hD1 : CartanMatrix.D (m + 5) i (⟨i.val - 1, by omega⟩ : Fin (m + 5)) = -1 := by
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
            split_ifs <;> (try simp only [true_or, or_true, true_and, and_true,
              not_true_eq_false, not_false_eq_true] at *) <;> omega
          have hj2 : (⟨i.val + 1, by omega⟩ : Fin (m + 5)) ≠ i := by
            intro hji
            have := congrArg Fin.val hji
            simp only [Fin.val_mk] at this
            omega
          have hD2 : CartanMatrix.D (m + 5) i (⟨i.val + 1, by omega⟩ : Fin (m + 5)) = -1 := by
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
            split_ifs <;> (try simp only [true_or, or_true, true_and, and_true,
              not_true_eq_false, not_false_eq_true] at *) <;> omega
          have h1 := eq_of_row_neg_one hrow hj1 hD1
          have h2 := eq_of_row_neg_one hrow hj2 hD2
          have hval := congrArg Fin.val (h1.trans h2.symm)
          simp only [Fin.val_mk] at hval
          omega

theorem ggLeafPos_D4 {i k : Fin 4} (h : GGLeafPos (CartanMatrix.D 4) i k) :
    k = 1 ∧ (i = 0 ∨ i = 2 ∨ i = 3) := by
  revert i k
  decide +kernel

end CFSG.StandardType

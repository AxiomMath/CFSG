module

public import CFSG.RankThree.Native.F5FourDimFormSpace

public section

namespace CFSG.RankThree.Native

open scoped Matrix

theorem f5H_pow_seven_mul : f5H ^ 7 * f5H = 1 := by
  decide +kernel

theorem f5X_pow_four_mul : f5X ^ 4 * f5X = 1 := by
  decide +kernel

@[expose] def f5I0Mat : Fin 5 → Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  ![f5X, f5H * f5X * f5H ^ 7, f5H ^ 2 * f5X * (f5H ^ 7) ^ 2, f5H ^ 3 * f5X * (f5H ^ 7) ^ 3,
    f5H ^ 4]

theorem f5_conj_pow_X_eq_pow_X {i j : ℕ} (hi : i < 5) (hj : j < 5)
    (h : f5H * f5X ^ 4 * f5H ^ 7 * f5X ^ i * (f5H * f5X * f5H ^ 7) = f5X ^ j) : i = 0 := by
  interval_cases i <;> interval_cases j <;> revert h <;> decide +kernel

private def f5PCdet4 (M : Matrix (Fin 4) (Fin 4) (ZMod 5)) : ZMod 5 :=
  M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
      M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)) -
    M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
      M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)) +
    M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) -
      M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) -
    M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) -
      M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))

private theorem f5PCdet4_eq_det (M : Matrix (Fin 4) (Fin 4) (ZMod 5)) :
    f5PCdet4 M = M.det := by
  simp only [f5PCdet4]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc, Fin.succ]
  simp
  ring

private def f5PCvm (v : Fin 4 → ZMod 5) (W : Matrix (Fin 4) (Fin 4) (ZMod 5)) :
    Fin 4 → ZMod 5 :=
  fun j => v 0 * W 0 j + v 1 * W 1 j + v 2 * W 2 j + v 3 * W 3 j

private theorem f5PCvm_eq_vecMul (v : Fin 4 → ZMod 5)
    (W : Matrix (Fin 4) (Fin 4) (ZMod 5)) : f5PCvm v W = v ᵥ* W := by
  funext j
  simp only [f5PCvm, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four]

private def f5PCa1 : Fin 4 → Fin 5 := ![2, 1, 3, 4]

private def f5PCb1 : Fin 4 → Fin 5 := ![3, 4, 2, 4]

private def f5PCa2 : Fin 4 → Fin 5 := ![0, 2, 4, 1]

private def f5PCb2 : Fin 4 → Fin 5 := ![3, 2, 2, 4]

private def f5PCW1 : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  ![!![0, 2, 3, 1; 0, 0, 0, 3; 3, 3, 1, 3; 4, 2, 3, 4],
    !![4, 2, 3, 4; 2, 2, 4, 2; 0, 4, 3, 4; 0, 3, 3, 2],
    !![3, 1, 1, 4; 3, 1, 0, 3; 0, 3, 1, 1; 1, 3, 0, 0],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]]

private def f5PCW2 : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  ![!![3, 1, 1, 0; 4, 2, 4, 2; 2, 3, 1, 3; 4, 0, 1, 4],
    !![1, 0, 4, 1; 2, 0, 0, 0; 1, 3, 3, 0; 3, 0, 4, 0],
    !![0, 1, 0, 1; 4, 4, 3, 0; 1, 4, 0, 2; 3, 4, 4, 2],
    !![4, 2, 3, 4; 2, 2, 4, 2; 0, 4, 3, 4; 0, 3, 3, 2]]

private theorem f5PCW1_eq (i : Fin 4) :
    f5PCW1 i = f5I0Mat (f5PCa1 i) * f5I0Mat (f5PCb1 i) := by
  fin_cases i <;> decide +kernel

private theorem f5PCW2_eq (i : Fin 4) :
    f5PCW2 i = f5I0Mat (f5PCa2 i) * f5I0Mat (f5PCb2 i) := by
  fin_cases i <;> decide +kernel

private theorem f5PC_check :
    ∀ a b c d : ZMod 5, ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) →
      f5PCdet4 (Matrix.of fun i => f5PCvm ![a, b, c, d] (f5PCW1 i)) ≠ 0 ∨
        f5PCdet4 (Matrix.of fun i => f5PCvm ![a, b, c, d] (f5PCW2 i)) ≠ 0 := by
  decide +kernel

theorem exists_det_rows_ne_zero {v : Fin 4 → ZMod 5} (hv : v ≠ 0) :
    ∃ a b : Fin 4 → Fin 5, (Matrix.of fun i => v ᵥ* f5I0Mat (a i) ᵥ* f5I0Mat (b i)).det ≠ 0 := by
  have hv' : ¬ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0) := by
    rintro ⟨h0, h1, h2, h3⟩
    apply hv
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  have hv_eq : v = ![v 0, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  have h := f5PC_check (v 0) (v 1) (v 2) (v 3) hv'
  rcases h with h | h
  · rw [f5PCdet4_eq_det] at h
    refine ⟨f5PCa1, f5PCb1, ?_⟩
    rw [hv_eq]
    have hmat :
        (Matrix.of fun i => ![v 0, v 1, v 2, v 3] ᵥ* f5I0Mat (f5PCa1 i) ᵥ*
            f5I0Mat (f5PCb1 i)) =
          Matrix.of fun i => f5PCvm ![v 0, v 1, v 2, v 3] (f5PCW1 i) := by
      ext i j
      simp only [Matrix.of_apply]
      rw [Matrix.vecMul_vecMul, ← f5PCW1_eq i, f5PCvm_eq_vecMul]
    rw [hmat]
    exact h
  · rw [f5PCdet4_eq_det] at h
    refine ⟨f5PCa2, f5PCb2, ?_⟩
    rw [hv_eq]
    have hmat :
        (Matrix.of fun i => ![v 0, v 1, v 2, v 3] ᵥ* f5I0Mat (f5PCa2 i) ᵥ*
            f5I0Mat (f5PCb2 i)) =
          Matrix.of fun i => f5PCvm ![v 0, v 1, v 2, v 3] (f5PCW2 i) := by
      ext i j
      simp only [Matrix.of_apply]
      rw [Matrix.vecMul_vecMul, ← f5PCW2_eq i, f5PCvm_eq_vecMul]
    rw [hmat]
    exact h

end CFSG.RankThree.Native

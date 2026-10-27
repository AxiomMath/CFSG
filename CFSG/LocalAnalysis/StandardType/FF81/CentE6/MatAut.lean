module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatD

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open Matrix

private theorem matAut_add_self (a : ZMod 2) : a + a = 0 := by
  have h : ∀ b : ZMod 2, b + b = 0 := by decide
  exact h a

private theorem matAut_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  exact h c

private theorem matAut_add_self_eight (a b c d : ZMod 2) : a + b + c + d + a + b + c + d = 0 := by
  rw [show a + b + c + d + a + b + c + d = (a + b + c + d) + (a + b + c + d) by ring]
  exact matAut_add_self _

private def matAut_succIdx (k : Fin 4) : Fin 6 := ⟨k.val + 1, by omega⟩

private def matAut_predIdx (i : Fin 6) : Fin 4 :=
  ⟨min (i.val - 1) 3, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private theorem matAut_succIdx_ne_zero (k : Fin 4) : matAut_succIdx k ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp [matAut_succIdx] at this

private theorem matAut_succIdx_ne_five (k : Fin 4) : matAut_succIdx k ≠ 5 := by
  intro h; have := congrArg Fin.val h; simp [matAut_succIdx] at this; omega

private theorem matAut_succIdx_inj {k l : Fin 4} (h : matAut_succIdx k = matAut_succIdx l) :
    k = l := by
  have := congrArg Fin.val h
  simp [matAut_succIdx] at this
  exact Fin.ext this

private theorem matAut_succIdx_predIdx {i : Fin 6} (h0 : i ≠ 0) (h5 : i ≠ 5) :
    matAut_succIdx (matAut_predIdx i) = i := by
  have hv0 : i.val ≠ 0 := fun h => h0 (Fin.ext (by simpa using h))
  have hv5 : i.val ≠ 5 := fun h => h5 (Fin.ext (by simpa using h))
  apply Fin.ext
  simp only [matAut_succIdx, matAut_predIdx, Fin.val_mk]
  rw [Nat.min_eq_left (by omega), Nat.sub_add_cancel (by omega)]

private noncomputable def matAut_x (a : Fin 4 → ZMod 2) (c : ZMod 2) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then 1 else if j = 5 then c else a (matAut_predIdx j))
    else if i = j then 1 else 0

private noncomputable def matAut_y (b : Fin 4 → ZMod 2) (c : ZMod 2) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j =>
    if j = 5 then (if i = 0 then c else if i = 5 then 1 else b (matAut_predIdx i))
    else if i = j then 1 else 0

private noncomputable def matAut_G (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then 1 else if j = 5 then 0 else w' (matAut_predIdx j))
    else if i = 5 then (if j = 5 then 1 else 0)
    else if j = 0 then 0
    else if j = 5 then (N (matAut_predIdx i) 0 * w 0 + N (matAut_predIdx i) 1 * w 1 +
      N (matAut_predIdx i) 2 * w 2 + N (matAut_predIdx i) 3 * w 3)
    else N (matAut_predIdx i) (matAut_predIdx j)

private noncomputable def matAut_G' (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then 1 else if j = 5 then
        (w' 0 * w 0 + w' 1 * w 1 + w' 2 * w 2 + w' 3 * w 3)
      else (w' 0 * M 0 (matAut_predIdx j) + w' 1 * M 1 (matAut_predIdx j) +
        w' 2 * M 2 (matAut_predIdx j) + w' 3 * M 3 (matAut_predIdx j)))
    else if i = 5 then (if j = 5 then 1 else 0)
    else if j = 0 then 0
    else if j = 5 then w (matAut_predIdx i)
    else M (matAut_predIdx i) (matAut_predIdx j)

private theorem matAut_x_row_zero (a : Fin 4 → ZMod 2) (c : ZMod 2) (j : Fin 6) :
    matAut_x a c 0 j = if j = 0 then 1 else if j = 5 then c else a (matAut_predIdx j) := by
  simp [matAut_x]

private theorem matAut_x_row_ne {m : Fin 6} (hm : m ≠ 0) (a : Fin 4 → ZMod 2) (c : ZMod 2)
    (j : Fin 6) : matAut_x a c m j = if m = j then 1 else 0 := by
  simp [matAut_x, hm]

private theorem matAut_y_col_five (b : Fin 4 → ZMod 2) (c : ZMod 2) (i : Fin 6) :
    matAut_y b c i 5 = if i = 0 then c else if i = 5 then 1 else b (matAut_predIdx i) := by
  simp [matAut_y]

private theorem matAut_y_col_ne (b : Fin 4 → ZMod 2) (c : ZMod 2) (i : Fin 6) {j : Fin 6}
    (hj : j ≠ 5) : matAut_y b c i j = if i = j then 1 else 0 := by
  simp [matAut_y, hj]

private theorem matAut_G_row0 (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) :
    matAut_G N w w' 0 j = if j = 0 then 1 else if j = 5 then 0 else w' (matAut_predIdx j) := by
  simp [matAut_G]

private theorem matAut_G_row1 (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) :
    matAut_G N w w' 1 j = if j = 0 then 0 else if j = 5 then
      (N 0 0 * w 0 + N 0 1 * w 1 + N 0 2 * w 2 + N 0 3 * w 3) else N 0 (matAut_predIdx j) := by
  simp [matAut_G, matAut_predIdx]

private theorem matAut_G_row2 (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) :
    matAut_G N w w' 2 j = if j = 0 then 0 else if j = 5 then
      (N 1 0 * w 0 + N 1 1 * w 1 + N 1 2 * w 2 + N 1 3 * w 3) else N 1 (matAut_predIdx j) := by
  simp [matAut_G, matAut_predIdx]

private theorem matAut_G_row3 (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) :
    matAut_G N w w' 3 j = if j = 0 then 0 else if j = 5 then
      (N 2 0 * w 0 + N 2 1 * w 1 + N 2 2 * w 2 + N 2 3 * w 3) else N 2 (matAut_predIdx j) := by
  simp [matAut_G, matAut_predIdx]

private theorem matAut_G_row4 (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) :
    matAut_G N w w' 4 j = if j = 0 then 0 else if j = 5 then
      (N 3 0 * w 0 + N 3 1 * w 1 + N 3 2 * w 2 + N 3 3 * w 3) else N 3 (matAut_predIdx j) := by
  simp [matAut_G, matAut_predIdx]

private theorem matAut_G_row5 (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) : matAut_G N w w' 5 j = if j = 5 then 1 else 0 := by
  simp [matAut_G]

private theorem matAut_G'_row0 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) :
    matAut_G' M w w' 0 j = if j = 0 then 1 else if j = 5 then
        (w' 0 * w 0 + w' 1 * w 1 + w' 2 * w 2 + w' 3 * w 3)
      else (w' 0 * M 0 (matAut_predIdx j) + w' 1 * M 1 (matAut_predIdx j) +
        w' 2 * M 2 (matAut_predIdx j) + w' 3 * M 3 (matAut_predIdx j)) := by
  simp [matAut_G']

private theorem matAut_G'_row1 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) :
    matAut_G' M w w' 1 j = if j = 0 then 0 else if j = 5 then w 0
      else M 0 (matAut_predIdx j) := by
  simp [matAut_G', matAut_predIdx]

private theorem matAut_G'_row2 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) :
    matAut_G' M w w' 2 j = if j = 0 then 0 else if j = 5 then w 1
      else M 1 (matAut_predIdx j) := by
  simp [matAut_G', matAut_predIdx]

private theorem matAut_G'_row3 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) :
    matAut_G' M w w' 3 j = if j = 0 then 0 else if j = 5 then w 2
      else M 2 (matAut_predIdx j) := by
  simp [matAut_G', matAut_predIdx]

private theorem matAut_G'_row4 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) :
    matAut_G' M w w' 4 j = if j = 0 then 0 else if j = 5 then w 3
      else M 3 (matAut_predIdx j) := by
  simp [matAut_G', matAut_predIdx]

private theorem matAut_G'_row5 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (j : Fin 6) : matAut_G' M w w' 5 j = if j = 5 then 1 else 0 := by
  simp [matAut_G']

private theorem matAut_four_sum {N M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hNM : N * M = 1)
    (a b : Fin 4) :
    N a 0 * M 0 b + N a 1 * M 1 b + N a 2 * M 2 b + N a 3 * M 3 b =
      if a = b then 1 else 0 := by
  have h : N a 0 * M 0 b + N a 1 * M 1 b + N a 2 * M 2 b + N a 3 * M 3 b =
      ∑ k : Fin 4, N a k * M k b := by rw [Fin.sum_univ_four]
  rw [h, ← Matrix.mul_apply, hNM]
  rw [Matrix.one_apply]

private theorem matAut_G_mul_G' (N M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (hNM : N * M = 1) : matAut_G N w w' * matAut_G' M w w' = 1 := by
  have e00 : N 0 0 * M 0 0 + N 0 1 * M 1 0 + N 0 2 * M 2 0 + N 0 3 * M 3 0 = 1 := by
    simpa using matAut_four_sum hNM 0 0
  have e01 : N 0 0 * M 0 1 + N 0 1 * M 1 1 + N 0 2 * M 2 1 + N 0 3 * M 3 1 = 0 := by
    simpa using matAut_four_sum hNM 0 1
  have e02 : N 0 0 * M 0 2 + N 0 1 * M 1 2 + N 0 2 * M 2 2 + N 0 3 * M 3 2 = 0 := by
    simpa using matAut_four_sum hNM 0 2
  have e03 : N 0 0 * M 0 3 + N 0 1 * M 1 3 + N 0 2 * M 2 3 + N 0 3 * M 3 3 = 0 := by
    simpa using matAut_four_sum hNM 0 3
  have e10 : N 1 0 * M 0 0 + N 1 1 * M 1 0 + N 1 2 * M 2 0 + N 1 3 * M 3 0 = 0 := by
    simpa using matAut_four_sum hNM 1 0
  have e11 : N 1 0 * M 0 1 + N 1 1 * M 1 1 + N 1 2 * M 2 1 + N 1 3 * M 3 1 = 1 := by
    simpa using matAut_four_sum hNM 1 1
  have e12 : N 1 0 * M 0 2 + N 1 1 * M 1 2 + N 1 2 * M 2 2 + N 1 3 * M 3 2 = 0 := by
    simpa using matAut_four_sum hNM 1 2
  have e13 : N 1 0 * M 0 3 + N 1 1 * M 1 3 + N 1 2 * M 2 3 + N 1 3 * M 3 3 = 0 := by
    simpa using matAut_four_sum hNM 1 3
  have e20 : N 2 0 * M 0 0 + N 2 1 * M 1 0 + N 2 2 * M 2 0 + N 2 3 * M 3 0 = 0 := by
    simpa using matAut_four_sum hNM 2 0
  have e21 : N 2 0 * M 0 1 + N 2 1 * M 1 1 + N 2 2 * M 2 1 + N 2 3 * M 3 1 = 0 := by
    simpa using matAut_four_sum hNM 2 1
  have e22 : N 2 0 * M 0 2 + N 2 1 * M 1 2 + N 2 2 * M 2 2 + N 2 3 * M 3 2 = 1 := by
    simpa using matAut_four_sum hNM 2 2
  have e23 : N 2 0 * M 0 3 + N 2 1 * M 1 3 + N 2 2 * M 2 3 + N 2 3 * M 3 3 = 0 := by
    simpa using matAut_four_sum hNM 2 3
  have e30 : N 3 0 * M 0 0 + N 3 1 * M 1 0 + N 3 2 * M 2 0 + N 3 3 * M 3 0 = 0 := by
    simpa using matAut_four_sum hNM 3 0
  have e31 : N 3 0 * M 0 1 + N 3 1 * M 1 1 + N 3 2 * M 2 1 + N 3 3 * M 3 1 = 0 := by
    simpa using matAut_four_sum hNM 3 1
  have e32 : N 3 0 * M 0 2 + N 3 1 * M 1 2 + N 3 2 * M 2 2 + N 3 3 * M 3 2 = 0 := by
    simpa using matAut_four_sum hNM 3 2
  have e33 : N 3 0 * M 0 3 + N 3 1 * M 1 3 + N 3 2 * M 2 3 + N 3 3 * M 3 3 = 1 := by
    simpa using matAut_four_sum hNM 3 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_six] <;>
    simp [matAut_G_row0, matAut_G_row1, matAut_G_row2, matAut_G_row3, matAut_G_row4,
      matAut_G_row5, matAut_G'_row0, matAut_G'_row1, matAut_G'_row2, matAut_G'_row3,
      matAut_G'_row4, matAut_G'_row5, matAut_predIdx, e00, e01, e02, e03, e10, e11, e12, e13,
      e20, e21, e22, e23, e30, e31, e32, e33, matAut_add_self, matAut_add_self_eight]

private theorem matAut_G_det (N M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (hNM : N * M = 1) : (matAut_G N w w').det = 1 := by
  have h := congrArg Matrix.det (matAut_G_mul_G' N M w w' hNM)
  rw [Matrix.det_mul, Matrix.det_one] at h
  rcases matAut_zero_or_one (matAut_G N w w').det with h0 | h1
  · rw [h0, zero_mul] at h
    exact absurd h (by decide)
  · exact h1

private theorem matAut_of_mem_Sone {g : SL(6, ZMod 2)} (hg : g ∈ Sone) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      matAut_x (fun l => g.1 0 (matAut_succIdx l)) (g.1 0 5) := by
  obtain ⟨h00, hrest⟩ := (mem_Sone_iff g).mp hg
  ext i j
  by_cases hi : i = 0
  · subst hi
    rw [matAut_x_row_zero]
    by_cases hj : j = 0
    · subst hj; rw [if_pos rfl]; exact h00
    · by_cases hj5 : j = 5
      · subst hj5
        rw [if_neg (by decide : (5 : Fin 6) ≠ 0), if_pos rfl]
      · rw [if_neg hj, if_neg hj5, matAut_succIdx_predIdx hj hj5]
  · rw [matAut_x_row_ne hi, hrest i j hi]

private theorem matAut_of_mem_Ssix {g : SL(6, ZMod 2)} (hg : g ∈ Ssix) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      matAut_y (fun l => g.1 (matAut_succIdx l) 5) (g.1 0 5) := by
  obtain ⟨h55, hrest⟩ := (mem_Ssix_iff g).mp hg
  ext i j
  by_cases hj5 : j = 5
  · subst hj5
    rw [matAut_y_col_five]
    by_cases hi : i = 0
    · subst hi; rw [if_pos rfl]
    · by_cases hi5 : i = 5
      · subst hi5
        rw [if_neg (by decide : (5 : Fin 6) ≠ 0), if_pos rfl]; exact h55
      · rw [if_neg hi, if_neg hi5, matAut_succIdx_predIdx hi hi5]
  · rw [matAut_y_col_ne _ _ _ hj5, hrest i j hj5]

private theorem matAut_vec_expand (M N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w : Fin 4 → ZMod 2)
    (k : Fin 4) :
    (M *ᵥ (N *ᵥ w)) k =
      M k 0 * (N 0 0 * w 0 + N 0 1 * w 1 + N 0 2 * w 2 + N 0 3 * w 3) +
      M k 1 * (N 1 0 * w 0 + N 1 1 * w 1 + N 1 2 * w 2 + N 1 3 * w 3) +
      M k 2 * (N 2 0 * w 0 + N 2 1 * w 1 + N 2 2 * w 2 + N 2 3 * w 3) +
      M k 3 * (N 3 0 * w 0 + N 3 1 * w 1 + N 3 2 * w 2 + N 3 3 * w 3) := by
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
  simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]

private theorem matAut_vec (M N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w : Fin 4 → ZMod 2)
    (hMN : M * N = 1) (k : Fin 4) :
    M k 0 * (N 0 0 * w 0 + N 0 1 * w 1 + N 0 2 * w 2 + N 0 3 * w 3) +
      M k 1 * (N 1 0 * w 0 + N 1 1 * w 1 + N 1 2 * w 2 + N 1 3 * w 3) +
      M k 2 * (N 2 0 * w 0 + N 2 1 * w 1 + N 2 2 * w 2 + N 2 3 * w 3) +
      M k 3 * (N 3 0 * w 0 + N 3 1 * w 1 + N 3 2 * w 2 + N 3 3 * w 3) = w k := by
  rw [← matAut_vec_expand, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]

private theorem matAut_sum_single (f : Fin 4 → ZMod 2) (k : Fin 4) :
    (if 0 = k then f 0 else 0) + (if 1 = k then f 1 else 0) + (if 2 = k then f 2 else 0) +
      (if 3 = k then f 3 else 0) = f k := by
  fin_cases k <;> simp

private theorem matAut_x_mul_G (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (a : Fin 4 → ZMod 2) :
    matAut_x a (a 0 * (N 0 0 * w 0 + N 0 1 * w 1 + N 0 2 * w 2 + N 0 3 * w 3) +
        a 1 * (N 1 0 * w 0 + N 1 1 * w 1 + N 1 2 * w 2 + N 1 3 * w 3) +
        a 2 * (N 2 0 * w 0 + N 2 1 * w 1 + N 2 2 * w 2 + N 2 3 * w 3) +
        a 3 * (N 3 0 * w 0 + N 3 1 * w 1 + N 3 2 * w 2 + N 3 3 * w 3)) *
        matAut_G N w w' =
      matAut_G N w w' * matAut_x
        (fun b => a 0 * N 0 b + a 1 * N 1 b + a 2 * N 2 b + a 3 * N 3 b) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_six] <;>
    simp [matAut_x_row_zero, matAut_x_row_ne, matAut_G_row0, matAut_G_row1, matAut_G_row2,
      matAut_G_row3, matAut_G_row4, matAut_G_row5, matAut_predIdx, matAut_add_self,
      matAut_add_self_eight] <;>
    try ring

private theorem matAut_y_mul_G (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (k : Fin 4) :
    matAut_y (fun j => N j k) (w' k) * matAut_G N w w' =
      matAut_G N w w' * matAut_y (Pi.single k 1) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_six] <;>
    simp [matAut_y_col_five, matAut_y_col_ne, matAut_G_row0, matAut_G_row1, matAut_G_row2,
      matAut_G_row3, matAut_G_row4, matAut_G_row5, matAut_predIdx, Pi.single_apply,
      matAut_sum_single, matAut_add_self] <;>
    try ring

private theorem matAut_t_mul_G (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2) :
    matAut_x (0 : Fin 4 → ZMod 2) 1 * matAut_G N w w' =
      matAut_G N w w' * matAut_x (0 : Fin 4 → ZMod 2) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_six] <;>
    simp [matAut_x_row_zero, matAut_x_row_ne, matAut_G_row0, matAut_G_row1, matAut_G_row2,
      matAut_G_row3, matAut_G_row4, matAut_G_row5, matAut_predIdx, matAut_add_self]

private def matAut_t : SL(6, ZMod 2) := CFSG.Holt.SL6.stdTransvection

private theorem matAut_t_coe : (matAut_t : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    1 + Matrix.single (0 : Fin 6) (5 : Fin 6) (1 : ZMod 2) :=
  CFSG.Holt.SL6.coe_stdTransvection

private theorem matAut_Sone_inf_Ssix : Sone ⊓ Ssix = Subgroup.zpowers matAut_t :=
  Sone_inf_Ssix

private theorem matAut_t_mem_Sone : matAut_t ∈ Sone := stdTransvection_mem_Sone

private theorem matAut_t_mem_Ssix : matAut_t ∈ Ssix := stdTransvection_mem_Ssix

private theorem matAut_t_sq : matAut_t * matAut_t = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, matAut_t_coe, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, Matrix.add_apply, Matrix.single, matAut_add_self]

private theorem matAut_fix_t1 (α : ↥Sgrp →* ↥Sgrp) (hα : Function.Injective α)
    (h1 : ∀ x : ↥Sgrp, (x : SL(6, ZMod 2)) ∈ Sone → ((α x : ↥Sgrp) : SL(6, ZMod 2)) ∈ Sone)
    (h6 : ∀ x : ↥Sgrp, (x : SL(6, ZMod 2)) ∈ Ssix → ((α x : ↥Sgrp) : SL(6, ZMod 2)) ∈ Ssix)
    (hS : matAut_t ∈ Sgrp) : α ⟨matAut_t, hS⟩ = ⟨matAut_t, hS⟩ := by
  have hmem : ((α ⟨matAut_t, hS⟩ : ↥Sgrp) : SL(6, ZMod 2)) ∈ Subgroup.zpowers matAut_t := by
    rw [← matAut_Sone_inf_Ssix, Subgroup.mem_inf]
    exact ⟨h1 _ matAut_t_mem_Sone, h6 _ matAut_t_mem_Ssix⟩
  rcases Subgroup.mem_zpowers_iff.mp hmem with ⟨n, hn⟩
  have h2 : matAut_t ^ (2 : ℤ) = 1 := by simpa [zpow_ofNat, pow_two] using matAut_t_sq
  have hmod : matAut_t ^ n = matAut_t ^ (n % 2) := zpow_eq_zpow_emod n h2
  have hne : ((α ⟨matAut_t, hS⟩ : ↥Sgrp) : SL(6, ZMod 2)) ≠ 1 := by
    intro hcon
    have hzero : α ⟨matAut_t, hS⟩ = 1 := Subtype.ext hcon
    have hα1 : α ⟨matAut_t, hS⟩ = α 1 := by rw [hzero, map_one]
    have hval : matAut_t = 1 := congrArg Subtype.val (hα hα1)
    have hmat : (matAut_t : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by rw [hval]; rfl
    rw [matAut_t_coe] at hmat
    have hentry := congrFun (congrFun hmat 0) 5
    simp [Matrix.add_apply] at hentry
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1'
  · exfalso
    apply hne
    rw [← hn, hmod, h0]
    simp
  · apply Subtype.ext
    rw [← hn, hmod, h1']
    simp

private theorem matAut_elem_coe (i j : Fin 6) (hij : i ≠ j) :
    ((elem i j : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + Matrix.single i j 1 := by
  rw [elem, dif_neg hij, Matrix.SpecialLinearGroup.transvection_coe]

private theorem matAut_elem_coe_zero_succ (k : Fin 4) :
    ((elem 0 (matAut_succIdx k) : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + Matrix.single 0 (matAut_succIdx k) 1 :=
  matAut_elem_coe 0 (matAut_succIdx k) (fun h => matAut_succIdx_ne_zero k h.symm)

private theorem matAut_elem_coe_succ_five (k : Fin 4) :
    ((elem (matAut_succIdx k) 5 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + Matrix.single (matAut_succIdx k) 5 1 :=
  matAut_elem_coe (matAut_succIdx k) 5 (matAut_succIdx_ne_five k)

private theorem matAut_mat_mul_same (i : Fin 6) (hi0 : i ≠ 0) :
    (1 + Matrix.single (0 : Fin 6) i (1 : ZMod 2)) *
        (1 + Matrix.single i (5 : Fin 6) (1 : ZMod 2)) =
      (1 + Matrix.single i (5 : Fin 6) (1 : ZMod 2)) *
        (1 + Matrix.single (0 : Fin 6) i (1 : ZMod 2)) *
        (1 + Matrix.single (0 : Fin 6) (5 : Fin 6) (1 : ZMod 2)) := by
  have hAB : Matrix.single (0 : Fin 6) i (1 : ZMod 2) * Matrix.single i (5 : Fin 6) 1 =
      Matrix.single (0 : Fin 6) (5 : Fin 6) 1 := by
    rw [Matrix.single_mul_single_same]; simp
  have hBA : Matrix.single i (5 : Fin 6) (1 : ZMod 2) * Matrix.single (0 : Fin 6) i 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := (by decide : (5 : Fin 6) ≠ 0))]
  have hBE : Matrix.single i (5 : Fin 6) (1 : ZMod 2) *
      Matrix.single (0 : Fin 6) (5 : Fin 6) 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := (by decide : (5 : Fin 6) ≠ 0))]
  have hAE : Matrix.single (0 : Fin 6) i (1 : ZMod 2) *
      Matrix.single (0 : Fin 6) (5 : Fin 6) 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hi0)]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hAB, hBA, hBE,
    hAE, Matrix.mul_zero, Matrix.zero_mul] <;> try abel

private theorem matAut_mat_mul_diff (i j : Fin 6) (hij : i ≠ j) :
    (1 + Matrix.single (0 : Fin 6) i (1 : ZMod 2)) *
        (1 + Matrix.single j (5 : Fin 6) (1 : ZMod 2)) =
      (1 + Matrix.single j (5 : Fin 6) (1 : ZMod 2)) *
        (1 + Matrix.single (0 : Fin 6) i (1 : ZMod 2)) := by
  have hAB : Matrix.single (0 : Fin 6) i (1 : ZMod 2) * Matrix.single j (5 : Fin 6) 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := hij)]
  have hBA : Matrix.single j (5 : Fin 6) (1 : ZMod 2) * Matrix.single (0 : Fin 6) i 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (h := (by decide : (5 : Fin 6) ≠ 0))]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hAB, hBA,
    Matrix.mul_zero, Matrix.zero_mul] <;> try abel

private theorem matAut_elem_comm (k l : Fin 4) :
    elem 0 (matAut_succIdx k) * elem (matAut_succIdx l) 5 =
      elem (matAut_succIdx l) 5 * elem 0 (matAut_succIdx k) *
        (if k = l then matAut_t else 1) := by
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      matAut_elem_coe_zero_succ, matAut_elem_coe_succ_five, matAut_t_coe]
    exact matAut_mat_mul_same _ (matAut_succIdx_ne_zero k)
  · rw [if_neg hkl]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_one, matAut_elem_coe_zero_succ, matAut_elem_coe_succ_five]
    exact matAut_mat_mul_diff _ _ (fun h => hkl (matAut_succIdx_inj h))

private theorem matAut_X_mul_Y (N M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (k l : Fin 4) :
    (matAut_x (M k) (w k) * matAut_y (fun j => N j l) (w' l)) 0 5 =
      w' l + M k 0 * N 0 l + M k 1 * N 1 l + M k 2 * N 2 l + M k 3 * N 3 l + w k := by
  rw [Matrix.mul_apply, Fin.sum_univ_six]
  simp [matAut_x, matAut_y, matAut_predIdx]
  try ring

private theorem matAut_Y_mul_X (N M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (k l : Fin 4) :
    (matAut_y (fun j => N j l) (w' l) * matAut_x (M k) (w k)) 0 5 = w k + w' l := by
  rw [Matrix.mul_apply, Fin.sum_univ_six]
  simp [matAut_x, matAut_y, matAut_predIdx]

private theorem matAut_Y_mul_X_zero (N M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (k l : Fin 4) :
    (matAut_y (fun j => N j l) (w' l) * matAut_x (M k) (w k)) 0 0 = 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_six]
  simp [matAut_x, matAut_y, matAut_predIdx]

private theorem matAut_mul_t_zero_five (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    (A * ((1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) +
        Matrix.single (0 : Fin 6) (5 : Fin 6) (1 : ZMod 2))) 0 5 = A 0 5 + A 0 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_six]
  simp [Matrix.single]

private theorem matAut_MN_one (X Y : Fin 4 → SL(6, ZMod 2))
    (M N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (hX : ∀ k, (X k).1 = matAut_x (M k) (w k))
    (hY : ∀ k, (Y k).1 = matAut_y (fun j => N j k) (w' k))
    (hXY : ∀ k l, X k * Y l = Y l * X k * (if k = l then matAut_t else 1)) :
    M * N = 1 := by
  ext k l
  have h : ((X k).1 * (Y l).1) 0 5 =
      ((Y l).1 * (X k).1 * (if k = l then matAut_t else 1).1) 0 5 :=
    congrArg (fun g : SL(6, ZMod 2) => g.1 0 5) (hXY k l)
  rw [hX k, hY l, matAut_X_mul_Y N M w w' k l] at h
  rw [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]
  split_ifs at h with hkl
  · rw [matAut_t_coe, matAut_mul_t_zero_five, matAut_Y_mul_X N M w w' k l,
      matAut_Y_mul_X_zero N M w w' k l] at h
    rw [if_pos hkl]
    linear_combination h
  · simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one] at h
    rw [matAut_Y_mul_X N M w w' k l] at h
    rw [if_neg hkl]
    linear_combination h

private theorem matAut_conj_of_gens (α : ↥Sgrp →* ↥Sgrp) (G : SL(6, ZMod 2))
    (hx : ∀ x : ↥Sgrp, (∃ j : Fin 6, 1 ≤ j.val ∧ (x : SL(6, ZMod 2)) = elem 0 j) →
      ((α x : ↥Sgrp) : SL(6, ZMod 2)) * G = G * x)
    (hy : ∀ x : ↥Sgrp, (∃ i : Fin 6, i.val ≤ 4 ∧ (x : SL(6, ZMod 2)) = elem i 5) →
      ((α x : ↥Sgrp) : SL(6, ZMod 2)) * G = G * x) (x : ↥Sgrp) :
    ((α x : ↥Sgrp) : SL(6, ZMod 2)) = G * x * G⁻¹ := by
  set φ₁ : ↥Sgrp →* SL(6, ZMod 2) := Sgrp.subtype.comp α with hφ₁
  set φ₂ : ↥Sgrp →* SL(6, ZMod 2) := (MulAut.conj G).toMonoidHom.comp Sgrp.subtype with hφ₂
  have hiff : ∀ y : ↥Sgrp, φ₁ y = φ₂ y ↔ ((α y : ↥Sgrp) : SL(6, ZMod 2)) * G = G * y := by
    intro y
    simp only [hφ₁, hφ₂, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact eq_mul_inv_iff_mul_eq
  have hE : ∀ y : ↥Sgrp, ((α y : ↥Sgrp) : SL(6, ZMod 2)) * G = G * y →
      (y : SL(6, ZMod 2)) ∈ (φ₁.eqLocus φ₂).map Sgrp.subtype :=
    fun y hy' => ⟨y, (hiff y).2 hy', rfl⟩
  have h1 : Sone ≤ (φ₁.eqLocus φ₂).map Sgrp.subtype := by
    rw [Sone, Subgroup.closure_le]
    rintro g ⟨j, hj, rfl⟩
    have hg : elem 0 j ∈ Sgrp := Subgroup.mem_sup_left (Subgroup.subset_closure ⟨j, hj, rfl⟩)
    exact hE ⟨_, hg⟩ (hx ⟨_, hg⟩ ⟨j, hj, rfl⟩)
  have h6 : Ssix ≤ (φ₁.eqLocus φ₂).map Sgrp.subtype := by
    rw [Ssix, Subgroup.closure_le]
    rintro g ⟨i, hi, rfl⟩
    have hg : elem i 5 ∈ Sgrp := Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, hi, rfl⟩)
    exact hE ⟨_, hg⟩ (hy ⟨_, hg⟩ ⟨i, hi, rfl⟩)
  have hS : Sgrp ≤ (φ₁.eqLocus φ₂).map Sgrp.subtype := sup_le h1 h6
  obtain ⟨x', hx', hxx'⟩ := hS x.2
  have hxx : x' = x := Subtype.ext hxx'
  have h3 : φ₁ x' = φ₂ x' := hx'
  rw [hxx] at h3
  rw [eq_mul_inv_iff_mul_eq]
  exact (hiff x).1 h3

private theorem matAut_mem_of_comm (G : SL(6, ZMod 2))
    (h : CFSG.Holt.SL6.stdTransvection * G = G * CFSG.Holt.SL6.stdTransvection) :
    G ∈ Sgrp ⊔ Jgrp := by
  rw [← centralizer_stdTransvection_eq, Subgroup.mem_centralizer_iff]
  rintro t (rfl : t = CFSG.Holt.SL6.stdTransvection)
  exact h

private theorem matAut_elem_zero_succ_eq (k : Fin 4) :
    ((elem 0 (matAut_succIdx k) : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      matAut_x (Pi.single k 1) 0 := by
  have hmem : elem 0 (matAut_succIdx k) ∈ Sone :=
    Subgroup.subset_closure ⟨matAut_succIdx k, by simp [matAut_succIdx], rfl⟩
  rw [matAut_of_mem_Sone hmem, matAut_elem_coe_zero_succ]
  congr 1
  · funext l
    rw [Matrix.add_apply, Matrix.one_apply_ne (fun h => matAut_succIdx_ne_zero l h.symm),
      zero_add, Matrix.single_apply, Pi.single_apply]
    by_cases hlk : l = k
    · subst hlk; simp
    · rw [if_neg (fun h => hlk (matAut_succIdx_inj h.2).symm), if_neg hlk]
  · rw [Matrix.add_apply, Matrix.one_apply_ne (by decide),
      Matrix.single_apply_of_col_ne 0 0 (matAut_succIdx_ne_five k) 1, add_zero]

private theorem matAut_elem_succ_five_eq (k : Fin 4) :
    ((elem (matAut_succIdx k) 5 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      matAut_y (Pi.single k 1) 0 := by
  have hmem : elem (matAut_succIdx k) 5 ∈ Ssix :=
    Subgroup.subset_closure ⟨matAut_succIdx k, by simp [matAut_succIdx], rfl⟩
  rw [matAut_of_mem_Ssix hmem, matAut_elem_coe_succ_five]
  congr 1
  · funext l
    rw [Matrix.add_apply, Matrix.one_apply_ne (matAut_succIdx_ne_five l), zero_add,
      Matrix.single_apply, Pi.single_apply]
    by_cases hlk : l = k
    · subst hlk; simp
    · rw [if_neg (fun h => hlk (matAut_succIdx_inj h.1).symm), if_neg hlk]

private theorem matAut_t_eq :
    (matAut_t : Matrix (Fin 6) (Fin 6) (ZMod 2)) = matAut_x 0 1 := by
  rw [matAut_of_mem_Sone matAut_t_mem_Sone, matAut_t_coe]
  congr 1
  · funext l
    rw [Matrix.add_apply, Matrix.one_apply_ne (fun h => matAut_succIdx_ne_zero l h.symm),
      Matrix.single_apply_of_col_ne 0 0 (fun h => matAut_succIdx_ne_five l h.symm) 1, add_zero,
      Pi.zero_apply]

private theorem matAut_x_gen (M N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w w' : Fin 4 → ZMod 2)
    (hMN : M * N = 1) (k : Fin 4) :
    matAut_x (M k) (w k) * matAut_G N w w' = matAut_G N w w' * matAut_x (Pi.single k 1) 0 := by
  have hrow : (fun b => M k 0 * N 0 b + M k 1 * N 1 b + M k 2 * N 2 b + M k 3 * N 3 b) =
      Pi.single k 1 := by
    funext b
    rw [matAut_four_sum hMN k b, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  have h := matAut_x_mul_G N w w' (M k)
  rwa [matAut_vec M N w hMN k, hrow] at h

private theorem matAut_map_comm (α : ↥Sgrp →* ↥Sgrp) (ht : matAut_t ∈ Sgrp)
    (hαt : α ⟨matAut_t, ht⟩ = ⟨matAut_t, ht⟩) {k l : Fin 4}
    (hx : elem 0 (matAut_succIdx k) ∈ Sgrp) (hy : elem (matAut_succIdx l) 5 ∈ Sgrp) :
    ((α ⟨_, hx⟩ : ↥Sgrp) : SL(6, ZMod 2)) * ((α ⟨_, hy⟩ : ↥Sgrp) : SL(6, ZMod 2)) =
      ((α ⟨_, hy⟩ : ↥Sgrp) : SL(6, ZMod 2)) * ((α ⟨_, hx⟩ : ↥Sgrp) : SL(6, ZMod 2)) *
        (if k = l then matAut_t else 1) := by
  have hrel : (⟨_, hx⟩ : ↥Sgrp) * ⟨_, hy⟩ =
      ⟨_, hy⟩ * ⟨_, hx⟩ * (if k = l then ⟨matAut_t, ht⟩ else 1) := by
    apply Subtype.ext
    have h := matAut_elem_comm k l
    split_ifs at h ⊢ <;> simpa using h
  have h := congrArg (fun z : ↥Sgrp => ((α z : ↥Sgrp) : SL(6, ZMod 2))) hrel
  simp only [map_mul, Subgroup.coe_mul] at h
  split_ifs at h ⊢
  · rwa [hαt] at h
  · simpa using h

private theorem matAut_exists_G (α : ↥Sgrp →* ↥Sgrp) (ht : matAut_t ∈ Sgrp)
    (hαt : α ⟨matAut_t, ht⟩ = ⟨matAut_t, ht⟩)
    (h1 : ∀ x : ↥Sgrp, (x : SL(6, ZMod 2)) ∈ Sone → ((α x : ↥Sgrp) : SL(6, ZMod 2)) ∈ Sone)
    (h6 : ∀ x : ↥Sgrp, (x : SL(6, ZMod 2)) ∈ Ssix → ((α x : ↥Sgrp) : SL(6, ZMod 2)) ∈ Ssix)
    (hxS : ∀ k : Fin 4, elem 0 (matAut_succIdx k) ∈ Sgrp)
    (hyS : ∀ k : Fin 4, elem (matAut_succIdx k) 5 ∈ Sgrp) :
    ∃ G : SL(6, ZMod 2),
      (∀ k, ((α ⟨_, hxS k⟩ : ↥Sgrp) : SL(6, ZMod 2)) * G = G * elem 0 (matAut_succIdx k)) ∧
      (∀ k, ((α ⟨_, hyS k⟩ : ↥Sgrp) : SL(6, ZMod 2)) * G = G * elem (matAut_succIdx k) 5) ∧
      matAut_t * G = G * matAut_t := by
  set X : Fin 4 → SL(6, ZMod 2) := fun k => (α ⟨_, hxS k⟩ : ↥Sgrp) with hXdef
  set Y : Fin 4 → SL(6, ZMod 2) := fun k => (α ⟨_, hyS k⟩ : ↥Sgrp) with hYdef
  let M : Matrix (Fin 4) (Fin 4) (ZMod 2) := fun k l => (X k).1 0 (matAut_succIdx l)
  let N : Matrix (Fin 4) (Fin 4) (ZMod 2) := fun j k => (Y k).1 (matAut_succIdx j) 5
  let w : Fin 4 → ZMod 2 := fun k => (X k).1 0 5
  let w' : Fin 4 → ZMod 2 := fun k => (Y k).1 0 5
  have hX : ∀ k, (X k).1 = matAut_x (M k) (w k) :=
    fun k => matAut_of_mem_Sone (h1 _ (Subgroup.subset_closure
      ⟨matAut_succIdx k, by simp [matAut_succIdx], rfl⟩))
  have hY : ∀ k, (Y k).1 = matAut_y (fun j => N j k) (w' k) :=
    fun k => matAut_of_mem_Ssix (h6 _ (Subgroup.subset_closure
      ⟨matAut_succIdx k, by simp [matAut_succIdx], rfl⟩))
  have hMN : M * N = 1 := matAut_MN_one X Y M N w w' hX hY
    (fun k l => matAut_map_comm α ht hαt (hxS k) (hyS l))
  refine ⟨⟨matAut_G N w w', matAut_G_det N M w w' (mul_eq_one_comm.mp hMN)⟩,
    fun k => ?_, fun k => ?_, ?_⟩
  · apply Subtype.ext
    show (X k).1 * matAut_G N w w' = matAut_G N w w' * (elem 0 (matAut_succIdx k)).1
    rw [hX k, matAut_elem_zero_succ_eq]
    exact matAut_x_gen M N w w' hMN k
  · apply Subtype.ext
    show (Y k).1 * matAut_G N w w' = matAut_G N w w' * (elem (matAut_succIdx k) 5).1
    rw [hY k, matAut_elem_succ_five_eq]
    exact matAut_y_mul_G N w w' k
  · apply Subtype.ext
    show matAut_t.1 * matAut_G N w w' = matAut_G N w w' * matAut_t.1
    rw [matAut_t_eq]
    exact matAut_t_mul_G N w w'

private theorem matAut_gen_zero (j : Fin 6) (hj : 1 ≤ j.val) :
    j = 5 ∨ ∃ k : Fin 4, j = matAut_succIdx k := by
  by_cases h5 : j = 5
  · exact Or.inl h5
  · exact Or.inr ⟨matAut_predIdx j, (matAut_succIdx_predIdx (by intro h; subst h; simp at hj)
      h5).symm⟩

private theorem matAut_gen_five (i : Fin 6) (hi : i.val ≤ 4) :
    i = 0 ∨ ∃ k : Fin 4, i = matAut_succIdx k := by
  by_cases h0 : i = 0
  · exact Or.inl h0
  · exact Or.inr ⟨matAut_predIdx i, (matAut_succIdx_predIdx h0
      (by intro h; subst h; simp at hi)).symm⟩

theorem exists_conj_eq_of_preserves (α : ↥Sgrp →* ↥Sgrp) (hα : Function.Injective α)
    (h1 : ∀ x : ↥Sgrp, (x : SL(6, ZMod 2)) ∈ Sone → ((α x : ↥Sgrp) : SL(6, ZMod 2)) ∈ Sone)
    (h6 : ∀ x : ↥Sgrp, (x : SL(6, ZMod 2)) ∈ Ssix → ((α x : ↥Sgrp) : SL(6, ZMod 2)) ∈ Ssix) :
    ∃ g ∈ Sgrp ⊔ Jgrp, ∀ x : ↥Sgrp,
      ((α x : ↥Sgrp) : SL(6, ZMod 2)) = g * (x : SL(6, ZMod 2)) * g⁻¹ := by
  have ht : matAut_t ∈ Sgrp := Subgroup.mem_sup_left matAut_t_mem_Sone
  have hαt := matAut_fix_t1 α hα h1 h6 ht
  have hxS : ∀ k : Fin 4, elem 0 (matAut_succIdx k) ∈ Sgrp := fun k =>
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, by simp [matAut_succIdx], rfl⟩)
  have hyS : ∀ k : Fin 4, elem (matAut_succIdx k) 5 ∈ Sgrp := fun k =>
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, by simp [matAut_succIdx], rfl⟩)
  obtain ⟨G, hGx, hGy, hGt⟩ := matAut_exists_G α ht hαt h1 h6 hxS hyS
  have htx : ∀ x : ↥Sgrp, (x : SL(6, ZMod 2)) = matAut_t →
      ((α x : ↥Sgrp) : SL(6, ZMod 2)) * G = G * x := by
    intro x hx
    obtain rfl : x = ⟨matAut_t, ht⟩ := Subtype.ext hx
    rw [hαt]
    exact hGt
  refine ⟨G, matAut_mem_of_comm G hGt, matAut_conj_of_gens α G ?_ ?_⟩
  · rintro x ⟨j, hj, hxj⟩
    rcases matAut_gen_zero j hj with rfl | ⟨k, rfl⟩
    · exact htx x hxj
    · obtain rfl : x = ⟨_, hxS k⟩ := Subtype.ext hxj
      exact hGx k
  · rintro x ⟨i, hi, hxi⟩
    rcases matAut_gen_five i hi with rfl | ⟨k, rfl⟩
    · exact htx x hxi
    · obtain rfl : x = ⟨_, hyS k⟩ := Subtype.ext hxi
      exact hGy k

end CFSG.StandardType.FF81.CentE6

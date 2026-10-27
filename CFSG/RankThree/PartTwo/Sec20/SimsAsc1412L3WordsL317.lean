module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3WordsLinExc
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Words

variable {K : Type} [Field K]

private def l317Yg : Matrix (Fin 3) (Fin 3) K := !![-1, -1, 0; -1, 0, -1; 0, -1, 0]

private def l317Yi : Matrix (Fin 3) (Fin 3) K := !![-1, -2, 0; -2, -1, -2; 0, -2, 1]

private theorem mat3_congr {K : Type} {a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : K}
    {b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : K}
    (h₁₁ : a₁₁ = b₁₁) (h₁₂ : a₁₂ = b₁₂) (h₁₃ : a₁₃ = b₁₃) (h₂₁ : a₂₁ = b₂₁) (h₂₂ : a₂₂ = b₂₂)
    (h₂₃ : a₂₃ = b₂₃) (h₃₁ : a₃₁ = b₃₁) (h₃₂ : a₃₂ = b₃₂) (h₃₃ : a₃₃ = b₃₃) :
    (!![a₁₁, a₁₂, a₁₃; a₂₁, a₂₂, a₂₃; a₃₁, a₃₂, a₃₃] : Matrix (Fin 3) (Fin 3) K) =
      !![b₁₁, b₁₂, b₁₃; b₂₁, b₂₂, b₂₃; b₃₁, b₃₂, b₃₃] := by
  subst h₁₁ h₁₂ h₁₃ h₂₁ h₂₂ h₂₃ h₃₁ h₃₂ h₃₃
  rfl

private theorem pow_eq_one_of_sq_chain_307 {G : Type*} [Monoid G]
    {m s2 s4 s8 s16 s32 s64 s128 s256 : G}
    (h2 : m * m = s2) (h4 : s2 * s2 = s4) (h8 : s4 * s4 = s8) (h16 : s8 * s8 = s16)
    (h32 : s16 * s16 = s32) (h64 : s32 * s32 = s64) (h128 : s64 * s64 = s128)
    (h256 : s128 * s128 = s256) (h : s256 * s32 * s16 * s2 * m = 1) :
    m ^ 307 = 1 := by
  have e2 : s2 = m ^ 2 := by rw [← h2, sq]
  have e4 : s4 = m ^ 4 := by rw [← h4, e2, ← pow_add]
  have e8 : s8 = m ^ 8 := by rw [← h8, e4, ← pow_add]
  have e16 : s16 = m ^ 16 := by rw [← h16, e8, ← pow_add]
  have e32 : s32 = m ^ 32 := by rw [← h32, e16, ← pow_add]
  have e64 : s64 = m ^ 64 := by rw [← h64, e32, ← pow_add]
  have e128 : s128 = m ^ 128 := by rw [← h128, e64, ← pow_add]
  have e256 : s256 = m ^ 256 := by rw [← h256, e128, ← pow_add]
  rw [← h, e256, e32, e16, e2, ← pow_add, ← pow_add, ← pow_add, ← pow_succ]

private theorem l317Yg_pow (h17 : (17 : K) = 0) :
    (l317Yg : Matrix (Fin 3) (Fin 3) K) ^ 307 = 1 := by
  show (!![-1, -1, 0; -1, 0, -1; 0, -1, 0] : Matrix (Fin 3) (Fin 3) K) ^ 307 = 1
  have h2 : (!![-1, -1, 0; -1, 0, -1; 0, -1, 0] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, -1, 0; -1, 0, -1; 0, -1, 0] =
      !![2, 1, 1; 1, 2, 0; 1, 0, 1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have h4 : (!![2, 1, 1; 1, 2, 0; 1, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![2, 1, 1; 1, 2, 0; 1, 0, 1] =
      !![6, 4, 3; 4, 5, 1; 3, 1, 2] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have h8 : (!![6, 4, 3; 4, 5, 1; 3, 1, 2] : Matrix (Fin 3) (Fin 3) K) *
      !![6, 4, 3; 4, 5, 1; 3, 1, 2] =
      !![-7, -4, -6; -4, 8, 2; -6, 2, -3] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (4) * h17)
      (by linear_combination (3) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (3) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (1) * h17)
  have h16 : (!![-7, -4, -6; -4, 8, 2; -6, 2, -3] : Matrix (Fin 3) (Fin 3) K) *
      !![-7, -4, -6; -4, 8, 2; -6, 2, -3] =
      !![-1, 1, 1; 1, -1, 0; 1, 0, -2] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (6) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (3) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (5) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (3) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (3) * h17)
  have h32 : (!![-1, 1, 1; 1, -1, 0; 1, 0, -2] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 1, 1; 1, -1, 0; 1, 0, -2] =
      !![3, -2, -3; -2, 2, 1; -3, 1, 5] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have h64 : (!![3, -2, -3; -2, 2, 1; -3, 1, 5] : Matrix (Fin 3) (Fin 3) K) *
      !![3, -2, -3; -2, 2, 1; -3, 1, 5] =
      !![5, 4, 8; 4, -8, -4; 8, -4, 1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (1) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (-2) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (-2) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (2) * h17)
  have h128 : (!![5, 4, 8; 4, -8, -4; 8, -4, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![5, 4, 8; 4, -8, -4; 8, -4, 1] =
      !![3, 7, -2; 7, -6, -8; -2, -8, -4] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (6) * h17)
      (by linear_combination (-3) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (-3) * h17)
      (by linear_combination (6) * h17)
      (by linear_combination (4) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (4) * h17)
      (by linear_combination (5) * h17)
  have h256 : (!![3, 7, -2; 7, -6, -8; -2, -8, -4] : Matrix (Fin 3) (Fin 3) K) *
      !![3, 7, -2; 7, -6, -8; -2, -8, -4] =
      !![-6, -5, -3; -5, -4, -2; -3, -2, -1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (4) * h17)
      (by linear_combination)
      (by linear_combination (-3) * h17)
      (by linear_combination)
      (by linear_combination (9) * h17)
      (by linear_combination (4) * h17)
      (by linear_combination (-3) * h17)
      (by linear_combination (4) * h17)
      (by linear_combination (5) * h17)
  have q1 : (!![-6, -5, -3; -5, -4, -2; -3, -2, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![3, -2, -3; -2, 2, 1; -3, 1, 5] =
      !![1, -1, -2; -1, 0, 1; -2, 1, 2] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have q2 : (!![1, -1, -2; -1, 0, 1; -2, 1, 2] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 1, 1; 1, -1, 0; 1, 0, -2] =
      !![-4, 2, 5; 2, -1, -3; 5, -3, -6] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have q3 : (!![-4, 2, 5; 2, -1, -3; 5, -3, -6] : Matrix (Fin 3) (Fin 3) K) *
      !![2, 1, 1; 1, 2, 0; 1, 0, 1] =
      !![-1, 0, 1; 0, 0, -1; 1, -1, -1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have q4 : (!![-1, 0, 1; 0, 0, -1; 1, -1, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, -1, 0; -1, 0, -1; 0, -1, 0] =
      !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  refine pow_eq_one_of_sq_chain_307 h2 h4 h8 h16 h32 h64 h128 h256 ?_
  rw [q1, q2, q3, q4]
  exact Matrix.one_fin_three.symm

private theorem l317Yi_pow (h17 : (17 : K) = 0) :
    (l317Yi : Matrix (Fin 3) (Fin 3) K) ^ 307 = 1 := by
  show (!![-1, -2, 0; -2, -1, -2; 0, -2, 1] : Matrix (Fin 3) (Fin 3) K) ^ 307 = 1
  have h2 : (!![-1, -2, 0; -2, -1, -2; 0, -2, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, -2, 0; -2, -1, -2; 0, -2, 1] =
      !![5, 4, 4; 4, -8, 0; 4, 0, 5] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination (1) * h17)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have h4 : (!![5, 4, 4; 4, -8, 0; 4, 0, 5] : Matrix (Fin 3) (Fin 3) K) *
      !![5, 4, 4; 4, -8, 0; 4, 0, 5] =
      !![6, 5, 6; 5, -5, -1; 6, -1, 7] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (3) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (5) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (2) * h17)
  have h8 : (!![6, 5, 6; 5, -5, -1; 6, -1, 7] : Matrix (Fin 3) (Fin 3) K) *
      !![6, 5, 6; 5, -5, -1; 6, -1, 7] =
      !![-5, -1, 5; -1, 0, -6; 5, -6, 1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (6) * h17)
      (by linear_combination)
      (by linear_combination (4) * h17)
      (by linear_combination)
      (by linear_combination (3) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (4) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (5) * h17)
  have h16 : (!![-5, -1, 5; -1, 0, -6; 5, -6, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![-5, -1, 5; -1, 0, -6; 5, -6, 1] =
      !![0, -8, 3; -8, 3, 6; 3, 6, -6] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (3) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (-1) * h17)
      (by linear_combination (4) * h17)
  have h32 : (!![0, -8, 3; -8, 3, 6; 3, 6, -6] : Matrix (Fin 3) (Fin 3) K) *
      !![0, -8, 3; -8, 3, 6; 3, 6, -6] =
      !![5, -6, 2; -6, 7, -8; 2, -8, -4] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (4) * h17)
      (by linear_combination)
      (by linear_combination (-4) * h17)
      (by linear_combination)
      (by linear_combination (6) * h17)
      (by linear_combination (-2) * h17)
      (by linear_combination (-4) * h17)
      (by linear_combination (-2) * h17)
      (by linear_combination (5) * h17)
  have h64 : (!![5, -6, 2; -6, 7, -8; 2, -8, -4] : Matrix (Fin 3) (Fin 3) K) *
      !![5, -6, 2; -6, 7, -8; 2, -8, -4] =
      !![-3, -3, -1; -3, -4, -2; -1, -2, -1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (4) * h17)
      (by linear_combination (-5) * h17)
      (by linear_combination (3) * h17)
      (by linear_combination (-5) * h17)
      (by linear_combination (9) * h17)
      (by linear_combination (-2) * h17)
      (by linear_combination (3) * h17)
      (by linear_combination (-2) * h17)
      (by linear_combination (5) * h17)
  have h128 : (!![-3, -3, -1; -3, -4, -2; -1, -2, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![-3, -3, -1; -3, -4, -2; -1, -2, -1] =
      !![2, 6, -7; 6, -5, -4; -7, -4, 6] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (1) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination)
  have h256 : (!![2, 6, -7; 6, -5, -4; -7, -4, 6] : Matrix (Fin 3) (Fin 3) K) *
      !![2, 6, -7; 6, -5, -4; -7, -4, 6] =
      !![4, -7, 5; -7, -8, 5; 5, 5, -1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (5) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (-5) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (5) * h17)
      (by linear_combination (-3) * h17)
      (by linear_combination (-5) * h17)
      (by linear_combination (-3) * h17)
      (by linear_combination (6) * h17)
  have q1 : (!![4, -7, 5; -7, -8, 5; 5, 5, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![5, -6, 2; -6, 7, -8; 2, -8, -4] =
      !![4, 6, -7; 6, -3, -4; -7, -4, 8] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (4) * h17)
      (by linear_combination (-7) * h17)
      (by linear_combination (3) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (-3) * h17)
      (by linear_combination (2) * h17)
      (by linear_combination)
      (by linear_combination (1) * h17)
      (by linear_combination (-2) * h17)
  have q2 : (!![4, 6, -7; 6, -3, -4; -7, -4, 8] : Matrix (Fin 3) (Fin 3) K) *
      !![0, -8, 3; -8, 3, 6; 3, 6, -6] =
      !![-1, -5, 5; -5, 4, 7; 5, 7, -8] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (-4) * h17)
      (by linear_combination (-3) * h17)
      (by linear_combination (5) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (-5) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (3) * h17)
      (by linear_combination (5) * h17)
      (by linear_combination (-5) * h17)
  have q3 : (!![-1, -5, 5; -5, 4, 7; 5, 7, -8] : Matrix (Fin 3) (Fin 3) K) *
      !![5, 4, 4; 4, -8, 0; 4, 0, 5] =
      !![-5, 2, 4; 2, -1, -2; 4, -2, -3] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination (2) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (-3) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (1) * h17)
      (by linear_combination (-2) * h17)
      (by linear_combination (-1) * h17)
  have q4 : (!![-5, 2, 4; 2, -1, -2; 4, -2, -3] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, -2, 0; -2, -1, -2; 0, -2, 1] =
      !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  refine pow_eq_one_of_sq_chain_307 h2 h4 h8 h16 h32 h64 h128 h256 ?_
  rw [q1, q2, q3, q4]
  exact Matrix.one_fin_three.symm

private theorem l317_word (h17 : (17 : K) = 0) :
    (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![0, 1, 0; -1, 0, -1; -1, -1, 0] *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * !![-1, 0, -1; 1, 0, 0; 1, -1, 1] *
      !![-1, 0, -1; 0, 0, 1; 0, 1, 1] * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] *
      !![-1, -1, 0; 0, -1, 1; 0, 1, 0] = l317Yi := by
  have p2 : (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![0, 1, 0; -1, 0, -1; -1, -1, 0] =
      !![0, -1, 0; 1, 0, 1; -1, -1, 0] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have p3 : (!![0, -1, 0; 1, 0, 1; -1, -1, 0] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      !![0, 1, 0; -1, 0, 1; 1, 1, 0] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have p4 : (!![0, 1, 0; -1, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, -1; 1, 0, 0; 1, -1, 1] =
      !![1, 0, 0; 2, -1, 2; 0, 0, -1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have p5 : (!![1, 0, 0; 2, -1, 2; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, -1; 0, 0, 1; 0, 1, 1] =
      !![-1, 0, -1; -2, 2, -1; 0, -1, -1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have p6 : (!![-1, 0, -1; -2, 2, -1; 0, -1, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      !![1, 0, -1; 2, -2, -1; 0, 1, -1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  have p7 : (!![1, 0, -1; 2, -2, -1; 0, 1, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, -1, 0; 0, -1, 1; 0, 1, 0] =
      !![-1, -2, 0; -2, -1, -2; 0, -2, 1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
  rw [p2, p3, p4, p5, p6, p7]
  rfl

end Words

variable [Fact (Nat.Prime 17)]

private theorem seventeen_eq_zero_L3_17 : (17 : GaloisField 17 1) = 0 := by
  have := CharP.cast_eq_zero (GaloisField 17 1) 17
  exact_mod_cast this

private theorem proj_injective_L3_17 : Function.Injective (proj 3 (GaloisField 17 1)) :=
  CFSG.RankThree.PartTwo.KFacts.proj_three_injective
    (by rw [GaloisField.card 17 1 one_ne_zero, pow_one])

private theorem orderOf_proj_L3_17 {M : SL(3, GaloisField 17 1)}
    (hM : (M : Matrix (Fin 3) (Fin 3) (GaloisField 17 1)) ^ 307 = 1)
    (h01 : (M : Matrix (Fin 3) (Fin 3) (GaloisField 17 1)) 0 1 ≠ 0) :
    orderOf (proj 3 _ M) = 307 := by
  have : Fact (Nat.Prime 307) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ fun h1 => h01 ?_
  · rw [← map_pow, show M ^ 307 = 1 from Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_pow, hM, Matrix.SpecialLinearGroup.coe_one]), map_one]
  · rw [proj_injective_L3_17 (h1.trans (map_one _).symm)]
    simp

private noncomputable def l317YgSL : SL(3, GaloisField 17 1) :=
  ⟨l317Yg, by simp [l317Yg, Matrix.det_fin_three]⟩

private noncomputable def l317YiSL : SL(3, GaloisField 17 1) :=
  ⟨l317Yi, by simp [l317Yi, Matrix.det_fin_three]⟩

private noncomputable def l317TSL : SL(3, GaloisField 17 1) :=
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private noncomputable def l317X₁SL : SL(3, GaloisField 17 1) :=
  ⟨!![0, 1, 0; -1, 0, -1; -1, -1, 0], by simp [Matrix.det_fin_three]⟩

private noncomputable def l317X₁iSL : SL(3, GaloisField 17 1) :=
  ⟨!![-1, 0, -1; 1, 0, 0; 1, -1, 1], by simp [Matrix.det_fin_three]⟩

private noncomputable def l317X₂SL : SL(3, GaloisField 17 1) :=
  ⟨!![-1, 0, -1; 0, 0, 1; 0, 1, 1], by simp [Matrix.det_fin_three]⟩

private noncomputable def l317X₂iSL : SL(3, GaloisField 17 1) :=
  ⟨!![-1, -1, 0; 0, -1, 1; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

private theorem coe_l317TSL :
    ((l317TSL : SL(3, GaloisField 17 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 17 1)) =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := rfl

private theorem coe_l317X₁SL :
    ((l317X₁SL : SL(3, GaloisField 17 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 17 1)) =
      !![0, 1, 0; -1, 0, -1; -1, -1, 0] := rfl

private theorem coe_l317X₁iSL :
    ((l317X₁iSL : SL(3, GaloisField 17 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 17 1)) =
      !![-1, 0, -1; 1, 0, 0; 1, -1, 1] := rfl

private theorem coe_l317X₂SL :
    ((l317X₂SL : SL(3, GaloisField 17 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 17 1)) =
      !![-1, 0, -1; 0, 0, 1; 0, 1, 1] := rfl

private theorem coe_l317X₂iSL :
    ((l317X₂iSL : SL(3, GaloisField 17 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 17 1)) =
      !![-1, -1, 0; 0, -1, 1; 0, 1, 0] := rfl

private theorem l317TSL_mul_self : l317TSL * l317TSL = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_l317TSL, Matrix.mul_apply, Fin.sum_univ_three]

private theorem l317X₁SL_mul : l317X₁SL * l317X₁iSL = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_l317X₁SL, coe_l317X₁iSL, Matrix.mul_apply,
    Fin.sum_univ_three]

private theorem l317X₂SL_mul : l317X₂SL * l317X₂iSL = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_l317X₂SL, coe_l317X₂iSL, Matrix.mul_apply,
    Fin.sum_univ_three]

private theorem l317_word_SL :
    l317TSL * l317X₁SL * l317TSL * l317X₁iSL * l317X₂SL * l317TSL * l317X₂iSL = l317YiSL :=
  Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact l317_word seventeen_eq_zero_L3_17)

private theorem orderOf_l317Yg : orderOf (proj 3 (GaloisField 17 1) l317YgSL) = 307 :=
  orderOf_proj_L3_17 (l317Yg_pow seventeen_eq_zero_L3_17) (by
    change (l317Yg : Matrix (Fin 3) (Fin 3) (GaloisField 17 1)) 0 1 ≠ 0
    simp [l317Yg])

private theorem orderOf_l317Yi : orderOf (proj 3 (GaloisField 17 1) l317YiSL) = 307 :=
  orderOf_proj_L3_17 (l317Yi_pow seventeen_eq_zero_L3_17) (by
    change (l317Yi : Matrix (Fin 3) (Fin 3) (GaloisField 17 1)) 0 1 ≠ 0
    have h17 := seventeen_eq_zero_L3_17
    simp only [l317Yi, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    intro h
    exact one_ne_zero (α := GaloisField 17 1) (by linear_combination h17 + 8 * h))

private theorem not_dvd_307 : ∀ e : ℕ, 1 ≤ e → e ≤ 12 → ¬ 307 ^ 1 ∣ 2 ^ e - 1 := by
  intro e he1 he12
  interval_cases e <;> norm_num

private theorem excl1412_dualAut_L3_17 : Excl1412 (dualAut 3 (GaloisField 17 1)) := by
  have hsym : (l317YgSL⁻¹).transpose = l317YgSL⁻¹ := by
    rw [inv_transpose_eq_transpose_inv_exc]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hδ : dualAut 3 (GaloisField 17 1) (proj 3 _ l317YgSL) = (proj 3 _ l317YgSL)⁻¹ := by
    rw [dualAut_proj, hsym, map_inv]
  refine Or.inl ⟨proj 3 _ l317YgSL, 307, 1, by norm_num, by norm_num, le_rfl,
    fun e he1 he8 => not_dvd_307 e he1 (by omega), ?_⟩
  rw [pow_one, hδ, ← _root_.mul_inv_rev, ← sq, orderOf_inv,
    Nat.Coprime.orderOf_pow (by rw [orderOf_l317Yg]; norm_num), orderOf_l317Yg]

private theorem excl1412_conj_L3_17 :
    Excl1412 (MulAut.conj (proj 3 (GaloisField 17 1) l317TSL)) := by
  have hτ : (proj 3 (GaloisField 17 1) l317TSL)⁻¹ = proj 3 _ l317TSL :=
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, l317TSL_mul_self, map_one])
  have hx₁ : (proj 3 (GaloisField 17 1) l317X₁SL)⁻¹ = proj 3 _ l317X₁iSL := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right l317X₁SL_mul]
  have hx₂ : (proj 3 (GaloisField 17 1) l317X₂SL)⁻¹ = proj 3 _ l317X₂iSL := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right l317X₂SL_mul]
  set τ := proj 3 (GaloisField 17 1) l317TSL with hτdef
  set x₁ := proj 3 (GaloisField 17 1) l317X₁SL with hx₁def
  set x₂ := proj 3 (GaloisField 17 1) l317X₂SL with hx₂def
  set a := MulAut.conj τ x₁ * x₁⁻¹ with hadef
  set b := MulAut.conj τ x₂ * x₂⁻¹ with hbdef
  have hy : τ * x₁ * τ * x₁⁻¹ * x₂ * τ * x₂⁻¹ = proj 3 _ l317YiSL := by
    rw [hx₁, hx₂, hτdef, hx₁def, hx₂def, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, l317_word_SL]
  have hw : a * b⁻¹ * a⁻¹ * b = proj 3 _ l317YiSL ^ 2 := by
    have e : a * b⁻¹ * a⁻¹ * b = (τ * x₁ * τ⁻¹ * x₁⁻¹ * x₂ * τ * x₂⁻¹) *
        (τ⁻¹ * x₁ * τ * x₁⁻¹ * x₂ * τ⁻¹ * x₂⁻¹) := by
      rw [hadef, hbdef, MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [e, hτ, hy, sq]
  have ha : a ∈ Subgroup.closure ({a, b} : Set (projectiveSL 3 (GaloisField 17 1))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : b ∈ Subgroup.closure ({a, b} : Set (projectiveSL 3 (GaloisField 17 1))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine Or.inr (Or.inl ⟨x₁, x₂, a * b⁻¹ * a⁻¹ * b, 307, 1, by norm_num, by norm_num, le_rfl,
    not_dvd_307,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb))
      (Subgroup.inv_mem _ ha)) hb, ?_⟩)
  rw [pow_one, hw, Nat.Coprime.orderOf_pow (by rw [orderOf_l317Yi]; norm_num), orderOf_l317Yi]

theorem excl1412_L3_17 (β : MulAut (projectiveSL 3 (GaloisField 17 1))) (hβ : orderOf β = 2) :
    Excl1412 β := by
  have ht : orderOf (proj 3 (GaloisField 17 1) l317TSL) = 2 := by
    refine orderOf_eq_prime (by rw [sq, ← map_mul, l317TSL_mul_self, map_one]) fun h1 => ?_
    have e := congrArg
      (fun g : SL(3, GaloisField 17 1) => (g : Matrix (Fin 3) (Fin 3) (GaloisField 17 1)) 0 0)
      (proj_injective_L3_17 (h1.trans (map_one _).symm))
    have h17 := seventeen_eq_zero_L3_17
    simp [coe_l317TSL] at e
    exact one_ne_zero (α := GaloisField 17 1) (by linear_combination h17 + 8 * e)
  exact excl1412_projectiveSL3_of_exc (p := 17) (by norm_num) ht excl1412_conj_L3_17
    excl1412_dualAut_L3_17 β hβ

end CFSG.RankThree.PartTwo.Sec20

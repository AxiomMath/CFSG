module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3WordsUniExc
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U37Group

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical

section Words

variable {K : Type} [Field K] {z : K}

private theorem mat3_congr {K : Type} {a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : K}
    {b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : K}
    (h₁₁ : a₁₁ = b₁₁) (h₁₂ : a₁₂ = b₁₂) (h₁₃ : a₁₃ = b₁₃) (h₂₁ : a₂₁ = b₂₁) (h₂₂ : a₂₂ = b₂₂)
    (h₂₃ : a₂₃ = b₂₃) (h₃₁ : a₃₁ = b₃₁) (h₃₂ : a₃₂ = b₃₂) (h₃₃ : a₃₃ = b₃₃) :
    (!![a₁₁, a₁₂, a₁₃; a₂₁, a₂₂, a₂₃; a₃₁, a₃₂, a₃₃] : Matrix (Fin 3) (Fin 3) K) =
      !![b₁₁, b₁₂, b₁₃; b₂₁, b₂₂, b₂₃; b₃₁, b₃₂, b₃₃] := by
  subst h₁₁ h₁₂ h₁₃ h₂₁ h₂₂ h₂₃ h₃₁ h₃₂ h₃₃
  rfl

private theorem det3_of (a b c d e f g h i : K) :
    (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) K).det =
      a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g := by
  simp [Matrix.det_fin_three]

private theorem pow_eq_one_of_sq_chain_43_7 {G : Type*} [Monoid G] {m s2 s4 s8 s16 s32 : G}
    (h2 : m * m = s2) (h4 : s2 * s2 = s4) (h8 : s4 * s4 = s8) (h16 : s8 * s8 = s16)
    (h32 : s16 * s16 = s32) (h : s32 * s8 * s2 * m = 1) :
    m ^ 43 = 1 := by
  have e2 : s2 = m ^ 2 := by rw [← h2, sq]
  have e4 : s4 = m ^ 4 := by rw [← h4, e2, ← pow_add]
  have e8 : s8 = m ^ 8 := by rw [← h8, e4, ← pow_add]
  have e16 : s16 = m ^ 16 := by rw [← h16, e8, ← pow_add]
  have e32 : s32 = m ^ 32 := by rw [← h32, e16, ← pow_add]
  rw [← h, e32, e8, e2, ← pow_add, ← pow_add, ← pow_succ]

private def u3x7X₁ (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 1 * z, 0, 1 * z; -1 * z, 0, 1 * z]

private def u3x7X₁i (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, -1 * z, 1 * z; 1, 0, 0; 0, -1 * z, -1 * z]

private def u3x7X₂ (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-3, -3 + -2 * z, 2 * z; 1 + -1 * z, -1, -3; 2 + -1 * z, -1 + -2 * z, 1 * z]

private def u3x7X₂i (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-3, 1 + 1 * z, 2 + 1 * z; -3 + 2 * z, -1, -1 + 2 * z; -2 * z, -3, -1 * z]

private def u3x7Y (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![3, 2 * z, 2; -2, -1 * z, 0; -2 * z, 3, -1 * z]

private theorem u3x7X₁_mul (hp : (7 : K) = 0) (hz : z ^ 2 = 3) :
    u3x7X₁ z * u3x7X₁i z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![0, 1, 0; 1 * z, 0, 1 * z; -1 * z, 0, 1 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![0, -1 * z, 1 * z; 1, 0, 0; 0, -1 * z, -1 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination)
    (by linear_combination)
    (by linear_combination)
    (by linear_combination)
    (by linear_combination (-2) * hz + (-1) * hp)
    (by linear_combination)
    (by linear_combination)
    (by linear_combination)
    (by linear_combination (-2) * hz + (-1) * hp)

private theorem u3x7X₁i_mul (hp : (7 : K) = 0) (hz : z ^ 2 = 3) :
    u3x7X₁i z * u3x7X₁ z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![0, -1 * z, 1 * z; 1, 0, 0; 0, -1 * z, -1 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![0, 1, 0; 1 * z, 0, 1 * z; -1 * z, 0, 1 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-2) * hz + (-1) * hp)
    (by linear_combination)
    (by linear_combination)
    (by linear_combination)
    (by linear_combination)
    (by linear_combination)
    (by linear_combination)
    (by linear_combination)
    (by linear_combination (-2) * hz + (-1) * hp)

private theorem u3x7X₂_mul (hp : (7 : K) = 0) (hz : z ^ 2 = 3) :
    u3x7X₂ z * u3x7X₂i z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![-3, -3 + -2 * z, 2 * z; 1 + -1 * z, -1, -3;
      2 + -1 * z, -1 + -2 * z, 1 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![-3, 1 + 1 * z, 2 + 1 * z; -3 + 2 * z, -1, -1 + 2 * z; -2 * z, -3, -1 * z] = !![1, 0, 0;
        0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-8) * hz + (-1) * hp)
    (by linear_combination (-1 * z) * hp)
    (by linear_combination (-6) * hz + (-3 + -1 * z) * hp)
    (by linear_combination (1 * z) * hp)
    (by linear_combination (-1) * hz + (1) * hp)
    (by linear_combination (-1) * hz)
    (by linear_combination (-6) * hz + (-3 + 1 * z) * hp)
    (by linear_combination (-1) * hz)
    (by linear_combination (-6) * hz + (-2) * hp)

private theorem u3x7X₂i_mul (hp : (7 : K) = 0) (hz : z ^ 2 = 3) :
    u3x7X₂i z * u3x7X₂ z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![-3, 1 + 1 * z, 2 + 1 * z; -3 + 2 * z, -1, -1 + 2 * z;
      -2 * z, -3, -1 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![-3, -3 + -2 * z, 2 * z; 1 + -1 * z, -1, -3; 2 + -1 * z, -1 + -2 * z, 1 * z] = !![1, 0, 0;
        0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-2) * hz + (1) * hp)
    (by linear_combination (-2) * hz)
    (by linear_combination (1) * hz + (-1 * z) * hp)
    (by linear_combination (-2) * hz)
    (by linear_combination (-8) * hz + (-2) * hp)
    (by linear_combination (6) * hz + (3 + -1 * z) * hp)
    (by linear_combination (1) * hz + (1 * z) * hp)
    (by linear_combination (6) * hz + (3 + 1 * z) * hp)
    (by linear_combination (-5) * hz + (-1) * hp)

private theorem det_u3x7X₁ (hp : (7 : K) = 0) (hz : z ^ 2 = 3) : (u3x7X₁ z).det = 1 := by
  rw [show u3x7X₁ z = !![0, 1, 0; 1 * z, 0, 1 * z; -1 * z, 0, 1 * z] from rfl, det3_of]
  linear_combination (-2) * hz + (-1) * hp

private theorem det_u3x7X₂ (hp : (7 : K) = 0) (hz : z ^ 2 = 3) : (u3x7X₂ z).det = 1 := by
  rw [show u3x7X₂ z = !![-3, -3 + -2 * z, 2 * z; 1 + -1 * z, -1, -3;
      2 + -1 * z, -1 + -2 * z, 1 * z] from rfl, det3_of]
  linear_combination (-11 + 2 * z) * hz + (-1 + 5 * z) * hp

private theorem map_u3x7X₁ (σ : K →+* K) (hσ : σ z = -z) :
    (u3x7X₁ z).map σ = (u3x7X₁i z)ᵀ := by
  rw [show u3x7X₁ z = !![0, 1, 0; 1 * z, 0, 1 * z; -1 * z, 0, 1 * z] from rfl, map_fin_three_of]
  rw [show (u3x7X₁i z)ᵀ = !![0, 1, 0; -1 * z, 0, -1 * z; 1 * z, 0, -1 * z] by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl]
  exact mat3_congr
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)

private theorem map_u3x7X₂ (σ : K →+* K) (hσ : σ z = -z) :
    (u3x7X₂ z).map σ = (u3x7X₂i z)ᵀ := by
  rw [show u3x7X₂ z = !![-3, -3 + -2 * z, 2 * z; 1 + -1 * z, -1, -3;
      2 + -1 * z, -1 + -2 * z, 1 * z] from rfl, map_fin_three_of]
  rw [show (u3x7X₂i z)ᵀ = !![-3, -3 + 2 * z, -2 * z; 1 + 1 * z, -1, -3;
      2 + 1 * z, -1 + 2 * z, -1 * z] by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl]
  exact mat3_congr
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)

private theorem u3x7_word (hp : (7 : K) = 0) (hz : z ^ 2 = 3) :
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * u3x7X₁ z * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * u3x7X₁i z *
      u3x7X₂ z * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * u3x7X₂i z = u3x7Y z := by
  rw [show u3x7X₁ z = !![0, 1, 0; 1 * z, 0, 1 * z; -1 * z, 0, 1 * z] from rfl,
    show u3x7X₁i z = !![0, -1 * z, 1 * z; 1, 0, 0; 0, -1 * z, -1 * z] from rfl,
    show u3x7X₂ z = !![-3, -3 + -2 * z, 2 * z; 1 + -1 * z, -1, -3;
        2 + -1 * z, -1 + -2 * z, 1 * z] from rfl,
    show u3x7X₂i z = !![-3, 1 + 1 * z, 2 + 1 * z; -3 + 2 * z, -1, -1 + 2 * z;
        -2 * z, -3, -1 * z] from rfl]
  have p2 : (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![0, 1, 0; 1 * z, 0, 1 * z; -1 * z, 0, 1 * z] =
      !![0, -1, 0; -1 * z, 0, -1 * z; -1 * z, 0, 1 * z] := by
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
  have p3 : (!![0, -1, 0; -1 *
      z, 0, -1 * z; -1 * z, 0, 1 * z] : Matrix (Fin 3) (Fin 3) K) * !![-1, 0, 0; 0, -1, 0;
          0, 0, 1] =
      !![0, 1, 0; 1 * z, 0, -1 * z; 1 * z, 0, 1 * z] := by
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
  have p4 : (!![0, 1, 0; 1 *
      z, 0, -1 * z; 1 * z, 0, 1 * z] : Matrix (Fin 3) (Fin 3) K) * !![0, -1 * z, 1 * z; 1, 0, 0;
          0, -1 * z, -1 * z] =
      !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination)
      (by linear_combination (2) * hz + (1) * hp)
      (by linear_combination)
      (by linear_combination (-2) * hz + (-1) * hp)
      (by linear_combination)
  have p5 : (!![1, 0, 0; 0, 0, -1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) *
      !![-3, -3 + -2 * z, 2 * z; 1 + -1 * z, -1, -3; 2 + -1 * z, -1 + -2 * z, 1 * z] =
      !![-3, -3 + -2 * z, 2 * z; -2 + 1 * z, 1 + 2 * z, -1 * z; 1 + -1 * z, -1, -3] := by
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
  have p6 : (!![-3, -3 + -2 *
      z, 2 * z; -2 + 1 * z, 1 + 2 * z, -1 * z; 1 + -1 * z, -1, -3] : Matrix (Fin 3) (Fin 3) K) *
          !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      !![3, 3 + 2 * z, 2 * z; 2 + -1 * z, -1 + -2 * z, -1 * z; -1 + 1 * z, 1, -3] := by
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
  have p7 : (!![3, 3 + 2 *
      z, 2 * z; 2 + -1 * z, -1 + -2 * z, -1 * z; -1 + 1 * z, 1, -3] : Matrix (Fin 3) (Fin 3) K) *
          !![-3, 1 + 1 * z, 2 + 1 * z; -3 + 2 * z, -1, -1 + 2 * z; -2 * z, -3, -1 * z] =
      !![3, 2 * z, 2; -2, -1 * z, 0; -2 * z, 3, -1 * z] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (-3) * hp)
      (by linear_combination (-1 * z) * hp)
      (by linear_combination (2) * hz + (1 + 1 * z) * hp)
      (by linear_combination (-2) * hz + (-1 + 1 * z) * hp)
      (by linear_combination (-1) * hz + (1 * z) * hp)
      (by linear_combination (-4) * hz + (-1) * hp)
      (by linear_combination (1 * z) * hp)
      (by linear_combination (1) * hz + (1) * hp)
      (by linear_combination (1) * hz + (1 * z) * hp)
  rw [p2, p3, p4, p5, p6, p7]
  rfl

private theorem u3x7Y_pow (hp : (7 : K) = 0) (hz : z ^ 2 = 3) : u3x7Y z ^ 43 = 1 := by
  show (!![3, 2 * z, 2; -2, -1 * z, 0; -2 * z, 3, -1 * z] : Matrix (Fin 3) (Fin 3) K) ^ 43 = 1
  have h2 : (!![3, 2 *
      z, 2; -2, -1 * z, 0; -2 * z, 3, -1 * z] : Matrix (Fin 3) (Fin 3) K) * !![3, 2 * z, 2;
          -2, -1 * z, 0; -2 * z, 3, -1 * z] =
      !![2 + -1 * z, -1 * z, -1 + -2 * z; 1 + 2 * z, 3 + 3 * z, 3;
          1 * z, 2 + 1 * z, 3 + 3 * z] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (1 + -1 * z) * hp)
      (by linear_combination (-2) * hz + (1 * z) * hp)
      (by linear_combination (1) * hp)
      (by linear_combination (-1) * hp)
      (by linear_combination (1) * hz + (-1 * z) * hp)
      (by linear_combination (-1) * hp)
      (by linear_combination (2) * hz + (-1 * z) * hp)
      (by linear_combination (-4) * hz + (-2 + -1 * z) * hp)
      (by linear_combination (1) * hz + (-1 * z) * hp)
  have h4 : (!![2 + -1 *
      z, -1 * z, -1 + -2 * z; 1 + 2 * z, 3 + 3 * z, 3; 1 * z, 2 + 1 * z, 3 + 3 *
          z] : Matrix (Fin 3) (Fin 3) K) * !![2 + -1 * z, -1 * z, -1 + -2 * z;
              1 + 2 * z, 3 + 3 * z, 3; 1 * z, 2 + 1 * z, 3 + 3 * z] =
      !![2 + 1 * z, -3 * z, -3 + -1 * z; 3 + 1 * z, 1 + -1 * z, -2;
          3 * z, -1 + -3 * z, 1 + -1 * z] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (-3) * hz + (-1 + -1 * z) * hp)
      (by linear_combination (-4) * hz + (-2 + -1 * z) * hp)
      (by linear_combination (-4) * hz + (-2 + -2 * z) * hp)
      (by linear_combination (4) * hz + (2 + 2 * z) * hp)
      (by linear_combination (7) * hz + (5 + 3 * z) * hp)
      (by linear_combination (-4) * hz + (1 + 2 * z) * hp)
      (by linear_combination (4) * hz + (2 + 1 * z) * hp)
      (by linear_combination (5) * hz + (4 + 3 * z) * hp)
      (by linear_combination (7) * hz + (5 + 3 * z) * hp)
  have h8 : (!![2 + 1 *
      z, -3 * z, -3 + -1 * z; 3 + 1 * z, 1 + -1 * z, -2; 3 * z, -1 + -3 * z, 1 + -1 *
          z] : Matrix (Fin 3) (Fin 3) K) * !![2 + 1 * z, -3 * z, -3 + -1 * z;
              3 + 1 * z, 1 + -1 * z, -2; 3 * z, -1 + -3 * z, 1 + -1 * z] =
      !![3, -2 + 1 * z, -2 + 3 * z; 2 + -3 * z, -3 + 2 * z, -2 + -2 * z;
          2 + -1 * z, 3 + 3 * z, -3 + 2 * z] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (-5) * hz + (-2 + -2 * z) * hp)
      (by linear_combination (3) * hz + (2) * hp)
      (by linear_combination (-1) * hp)
      (by linear_combination (1) * hp)
      (by linear_combination (-2) * hz + (-1 * z) * hp)
      (by linear_combination (-1) * hz + (-2) * hp)
      (by linear_combination (-3) * hz + (-2) * hp)
      (by linear_combination (-3) * hz + (-2 + -1 * z) * hp)
      (by linear_combination (-2) * hz + (-1 * z) * hp)
  have h16 : (!![3, -2 + 1 *
      z, -2 + 3 * z; 2 + -3 * z, -3 + 2 * z, -2 + -2 * z; 2 + -1 * z, 3 + 3 * z, -3 + 2 *
          z] : Matrix (Fin 3) (Fin 3) K) * !![3, -2 + 1 * z, -2 + 3 * z;
              2 + -3 * z, -3 + 2 * z, -2 + -2 * z; 2 + -1 * z, 3 + 3 * z, -3 + 2 * z] =
      !![-3 + 2 * z, -1 + -1 * z, 2 + -2 * z; -2 + 2 * z, -2 + -2 * z, -1 + 2 * z;
          1 + 1 * z, -3 + -2 * z, -2 + -2 * z] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (-6) * hz + (-2 + 2 * z) * hp)
      (by linear_combination (11) * hz + (4) * hp)
      (by linear_combination (4) * hz + (2) * hp)
      (by linear_combination (-4) * hz + (-2) * hp)
      (by linear_combination (-5) * hz + (-2 + -2 * z) * hp)
      (by linear_combination (-17) * hz + (-6 + 2 * z) * hp)
      (by linear_combination (-11) * hz + (-4) * hp)
      (by linear_combination (11) * hz + (2) * hp)
      (by linear_combination (-5) * hz + (-2 + -2 * z) * hp)
  have h32 : (!![-3 + 2 *
      z, -1 + -1 * z, 2 + -2 * z; -2 + 2 * z, -2 + -2 * z, -1 + 2 * z; 1 + 1 * z, -3 + -2 *
          z, -2 + -2 * z] : Matrix (Fin 3) (Fin 3) K) * !![-3 + 2 * z, -1 + -1 * z, 2 + -2 * z;
              -2 + 2 * z, -2 + -2 * z, -1 + 2 * z; 1 + 1 * z, -3 + -2 * z, -2 + -2 * z] =
      !![-1 + 2 * z, -3, -1 + 2 * z; 1 + -2 * z, 3 + -3 * z, -1 + -3 * z;
          3, -3 + -3 * z, 3 + -3 * z] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (2 + -2 * z) * hp)
      (by linear_combination (4) * hz + (2 + 1 * z) * hp)
      (by linear_combination (-2) * hz + (-2 + 1 * z) * hp)
      (by linear_combination (2) * hz + (2 + -1 * z) * hp)
      (by linear_combination (-2) * hz + (1 * z) * hp)
      (by linear_combination (-12) * hz + (-5 + 1 * z) * hp)
      (by linear_combination (-4) * hz + (-2 + -1 * z) * hp)
      (by linear_combination (7) * hz + (5 + 3 * z) * hp)
      (by linear_combination (-2) * hz + (1 * z) * hp)
  have q1 : (!![-1 + 2 *
      z, -3, -1 + 2 * z; 1 + -2 * z, 3 + -3 * z, -1 + -3 * z; 3, -3 + -3 * z, 3 + -3 *
          z] : Matrix (Fin 3) (Fin 3) K) * !![3, -2 + 1 * z, -2 + 3 * z;
              2 + -3 * z, -3 + 2 * z, -2 + -2 * z; 2 + -1 * z, 3 + 3 * z, -3 + 2 * z] =
      !![-3 + -1 * z, -3 + -1 * z, -1 + -2 * z; 1 + 2 * z, -2 + 1 * z, -2;
          3 + 1 * z, 2 + -1 * z, -2 + 1 * z] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (-2) * hz + (-2 + 3 * z) * hp)
      (by linear_combination (8) * hz + (5 + -1 * z) * hp)
      (by linear_combination (10) * hz + (6 + -1 * z) * hp)
      (by linear_combination (12) * hz + (6 + -4 * z) * hp)
      (by linear_combination (-17) * hz + (-9 + 1 * z) * hp)
      (by linear_combination (-6) * hz + (-3 + 2 * z) * hp)
      (by linear_combination (12) * hz + (6 + -1 * z) * hp)
      (by linear_combination (-15) * hz + (-5 + 1 * z) * hp)
      (by linear_combination (-1 + 5 * z) * hp)
  have q2 : (!![-3 + -1 *
      z, -3 + -1 * z, -1 + -2 * z; 1 + 2 * z, -2 + 1 * z, -2; 3 + 1 * z, 2 + -1 * z, -2 + 1 *
          z] : Matrix (Fin 3) (Fin 3) K) * !![2 + -1 * z, -1 * z, -1 + -2 * z;
              1 + 2 * z, 3 + 3 * z, 3; 1 * z, 2 + 1 * z, 3 + 3 * z] =
      !![3, -2, 2 * z; -2 * z, 1 * z, 3; 2, 0, 1 * z] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (-3) * hz + (-3 + -1 * z) * hp)
      (by linear_combination (-4) * hz + (-3 + -2 * z) * hp)
      (by linear_combination (-4) * hz + (-3 + -1 * z) * hp)
      (by linear_combination)
      (by linear_combination (1) * hz + (-1 + -1 * z) * hp)
      (by linear_combination (-4) * hz + (-4 + -1 * z) * hp)
      (by linear_combination (-2) * hz)
      (by linear_combination (-3) * hz + (-1) * hp)
      (by linear_combination (1) * hz + (-2 * z) * hp)
  have q3 : (!![3, -2, 2 *
      z; -2 * z, 1 * z, 3; 2, 0, 1 * z] : Matrix (Fin 3) (Fin 3) K) * !![3, 2 * z, 2;
          -2, -1 * z, 0; -2 * z, 3, -1 * z] =
      !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
    rw [Matrix.mul_fin_three]
    exact mat3_congr
      (by linear_combination (-4) * hz)
      (by linear_combination (2 * z) * hp)
      (by linear_combination (-2) * hz)
      (by linear_combination (-2 * z) * hp)
      (by linear_combination (-5) * hz + (-1) * hp)
      (by linear_combination (-1 * z) * hp)
      (by linear_combination (-2) * hz)
      (by linear_combination (1 * z) * hp)
      (by linear_combination (-1) * hz)
  refine pow_eq_one_of_sq_chain_43_7 h2 h4 h8 h16 h32 ?_
  rw [q1, q2, q3]
  exact Matrix.one_fin_three.symm

private theorem u3x7Y_ne_one (hp : (7 : K) = 0) (hz : z ^ 2 = 3) : u3x7Y z ≠ 1 := by
  intro h1
  have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) h1
  simp [u3x7Y] at e
  exact one_ne_zero (α := K) (by linear_combination (-3) * e + (1) * hp)

end Words

section Group

variable {K : Type} [Field K]

private theorem negNegOneDiag_eq_u3x7 :
    negNegOneDiag K = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negNegOneDiag]

private def u3x7X₁SU (h : UnitaryFieldData 7 1 K) {z : K} (hp : (7 : K) = 0) (hz : z ^ 2 = 3)
    (hbar : h.bar z = -z) : unitarySU 7 1 K 3 :=
  ⟨⟨u3x7X₁ z, u3x7X₁i z, u3x7X₁_mul hp hz, u3x7X₁i_mul hp hz⟩,
    (mem_unitarySU_iff h).mpr ⟨det_u3x7X₁ hp hz, by
      change ((u3x7X₁ z).map h.bar)ᵀ * u3x7X₁ z = 1
      rw [map_u3x7X₁ h.bar hbar, Matrix.transpose_transpose, u3x7X₁i_mul hp hz]⟩⟩

private def u3x7X₂SU (h : UnitaryFieldData 7 1 K) {z : K} (hp : (7 : K) = 0) (hz : z ^ 2 = 3)
    (hbar : h.bar z = -z) : unitarySU 7 1 K 3 :=
  ⟨⟨u3x7X₂ z, u3x7X₂i z, u3x7X₂_mul hp hz, u3x7X₂i_mul hp hz⟩,
    (mem_unitarySU_iff h).mpr ⟨det_u3x7X₂ hp hz, by
      change ((u3x7X₂ z).map h.bar)ᵀ * u3x7X₂ z = 1
      rw [map_u3x7X₂ h.bar hbar, Matrix.transpose_transpose, u3x7X₂i_mul hp hz]⟩⟩

private theorem excl1412_conj_U3_7 (h : UnitaryFieldData 7 1 K) {z : K} (hp : (7 : K) =
    0) (hz : z ^ 2 = 3)
    (hbar : h.bar z = -z) : Excl1412 (MulAut.conj (unitaryProj h 3 (unitaryInvT h))) := by
  have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  set x₁ := u3x7X₁SU h hp hz hbar with hx₁def
  set x₂ := u3x7X₂SU h hp hz hbar with hx₂def
  set τ := unitaryProj h 3 (unitaryInvT h) with hτdef
  have hτ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by
    rw [hτdef, ← map_mul, ← sq, unitaryInvT_sq, map_one])
  set y : unitarySU 7 1 K 3 :=
    unitaryInvT h * x₁ * unitaryInvT h * x₁⁻¹ * x₂ * unitaryInvT h * x₂⁻¹ with hydef
  have hy : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u3x7Y z := by
    rw [hydef, ← u3x7_word hp hz, ← negNegOneDiag_eq_u3x7, ← coe_unitaryInvT h]
    rfl
  have hyo : orderOf (unitaryProj h 3 y) = 43 := by
    rw [orderOf_injective _ (unitaryProj_injective_exc h (by norm_num)) y, ← Subgroup.orderOf_coe,
      ← orderOf_units, hy]
    exact orderOf_eq_prime (u3x7Y_pow hp hz) (u3x7Y_ne_one hp hz)
  set a := MulAut.conj τ (unitaryProj h 3 x₁) * (unitaryProj h 3 x₁)⁻¹ with hadef
  set b := MulAut.conj τ (unitaryProj h 3 x₂) * (unitaryProj h 3 x₂)⁻¹ with hbdef
  have hw : a * b⁻¹ * a⁻¹ * b = unitaryProj h 3 y ^ 2 := by
    have e : a * b⁻¹ * a⁻¹ * b =
        (τ * unitaryProj h 3 x₁ * τ⁻¹ * (unitaryProj h 3 x₁)⁻¹ * unitaryProj h 3 x₂ * τ *
          (unitaryProj h 3 x₂)⁻¹) *
        (τ⁻¹ * unitaryProj h 3 x₁ * τ * (unitaryProj h 3 x₁)⁻¹ * unitaryProj h 3 x₂ * τ⁻¹ *
          (unitaryProj h 3 x₂)⁻¹) := by
      rw [hadef, hbdef, MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [e, hτ, sq, hydef, hτdef]
    simp only [map_mul, map_inv]
  have ha : a ∈ Subgroup.closure ({a, b} : Set (unitaryPSU h 3)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : b ∈ Subgroup.closure ({a, b} : Set (unitaryPSU h 3)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine Or.inr (Or.inl ⟨unitaryProj h 3 x₁, unitaryProj h 3 x₂, a * b⁻¹ * a⁻¹ * b, 43, 1,
    by norm_num, by norm_num, le_rfl, fun e he1 he12 => by
      interval_cases e <;> norm_num,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb))
      (Subgroup.inv_mem _ ha)) hb, ?_⟩)
  rw [pow_one, hw, Nat.Coprime.orderOf_pow (by rw [hyo]; norm_num), hyo]

end Group

theorem excl1412_U3_7 (K : Type) [Field K] (h : UnitaryFieldData 7 1 K)
    (α : MulAut (unitaryPSU h 3)) (hα : orderOf α = 2) : Excl1412 α := by
  obtain ⟨h7, z, hz, hbar⟩ := exists_sq_eq_three_of_unitary_seven h
  have h43 : orderOf (u37YGL h7 hz) = 43 := by
    have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    rw [← orderOf_units]
    refine orderOf_eq_prime (u37Y_pow_fortyThree h7 hz) fun h1 => u37Y_zero_one_ne_zero h7 hz ?_
    have e : (u37Y z : Matrix (Fin 3) (Fin 3) K) 0 1 = (1 : Matrix (Fin 3) (Fin 3) K) 0 1 :=
      congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 1) h1
    simpa using e
  exact excl1412_unitaryPSU3_of_exc h (by norm_num) (excl1412_conj_U3_7 h h7 hz hbar)
    (u37YGL_mem h h7 hz hbar) (transpose_u37Y z) (q := 43) (k := 1) (by norm_num) (by norm_num)
    le_rfl (fun e he1 he8 => by interval_cases e <;> norm_num) (by rw [pow_one, h43]) α hα

end CFSG.RankThree.PartTwo.Sec20

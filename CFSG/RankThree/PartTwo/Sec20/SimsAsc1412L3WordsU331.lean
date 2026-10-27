module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3WordsUniExc
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U37Words

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

private theorem pow_eq_one_of_sq_chain_19_31 {G : Type*} [Monoid G] {m s2 s4 s8 s16 : G}
    (h2 : m * m = s2) (h4 : s2 * s2 = s4) (h8 : s4 * s4 = s8) (h16 : s8 * s8 = s16)
    (h : s16 * s2 * m = 1) :
    m ^ 19 = 1 := by
  have e2 : s2 = m ^ 2 := by rw [← h2, sq]
  have e4 : s4 = m ^ 4 := by rw [← h4, e2, ← pow_add]
  have e8 : s8 = m ^ 8 := by rw [← h8, e4, ← pow_add]
  have e16 : s16 = m ^ 16 := by rw [← h16, e8, ← pow_add]
  rw [← h, e16, e2, ← pow_add, ← pow_succ]

private def u3x31X₁ (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-6 + -8 * z, 1 + 4 * z, 15; -5 + 2 * z, 3, 3 + -4 * z; 5 + -8 * z, 6 + 1 * z, -5 + 6 * z]

private def u3x31X₁i (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-6 + 8 * z, -5 + -2 * z, 5 + 8 * z; 1 + -4 * z, 3, 6 + -1 * z; 15, 3 + 4 * z, -5 + -6 * z]

private def u3x31X₂ (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![4 + 1 * z, -3 + 2 * z, 9 + 13 * z; -7 + -6 * z, 5, 14 + 6 * z;
      -6 + -7 * z, -4 + -3 * z, -13 + -1 * z]

private def u3x31X₂i (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![4 + -1 * z, -7 + 6 * z, -6 + 7 * z; -3 + -2 * z, 5, -4 + 3 * z;
      9 + -13 * z, 14 + -6 * z, -13 + 1 * z]

private def u3x31Y (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-2 + -13 * z, -6, 8 + 10 * z; 15 + -1 * z, 4 + -9 * z, -5 + 5 * z;
      1 + -2 * z, -7 + 6 * z, -4 + 9 * z]

private def u3x31Yf (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-5, 3 + 1 * z, 9 + -3 * z; 3 + 1 * z, -9 + 1 * z, 8; 9 + -3 * z, 8, 6 + 11 * z]

private def u3x31Yfi (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-5, 3 + -1 * z, 9 + 3 * z; 3 + -1 * z, -9 + -1 * z, 8; 9 + 3 * z, 8, 6 + -11 * z]

private theorem u3x31X₁_mul (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    u3x31X₁ z * u3x31X₁i z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![-6 + -8 * z, 1 + 4 * z, 15; -5 + 2 * z, 3, 3 + -4 * z;
      5 + -8 * z, 6 + 1 * z, -5 + 6 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![-6 + 8 * z, -5 + -2 * z, 5 + 8 * z; 1 + -4 * z, 3, 6 + -1 * z;
        15, 3 + 4 * z, -5 + -6 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-80) * hz + (11) * hp)
    (by linear_combination (16) * hz + (2 + 4 * z) * hp)
    (by linear_combination (-68) * hz + (-1 + -5 * z) * hp)
    (by linear_combination (16) * hz + (2 + -4 * z) * hp)
    (by linear_combination (-20) * hz + (2) * hp)
    (by linear_combination (40) * hz + (-2 + -1 * z) * hp)
    (by linear_combination (-68) * hz + (-1 + 5 * z) * hp)
    (by linear_combination (40) * hz + (-2 + 1 * z) * hp)
    (by linear_combination (-101) * hz + (6) * hp)

private theorem u3x31X₁i_mul (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    u3x31X₁i z * u3x31X₁ z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![-6 + 8 * z, -5 + -2 * z, 5 + 8 * z; 1 + -4 * z, 3, 6 + -1 * z;
      15, 3 + 4 * z, -5 + -6 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![-6 + -8 * z, 1 + 4 * z, 15; -5 + 2 * z, 3, 3 + -4 * z;
        5 + -8 * z, 6 + 1 * z, -5 + 6 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-132) * hz + (7) * hp)
    (by linear_combination (40) * hz + (-1 + 1 * z) * hp)
    (by linear_combination (56) * hz + (-6 + 4 * z) * hp)
    (by linear_combination (40) * hz + (-1 + -1 * z) * hp)
    (by linear_combination (-17) * hz + (2) * hp)
    (by linear_combination (-6) * hz + (-1 * z) * hp)
    (by linear_combination (56) * hz + (-6 + -4 * z) * hp)
    (by linear_combination (-6) * hz + (1 * z) * hp)
    (by linear_combination (-52) * hz + (10) * hp)

private theorem u3x31X₂_mul (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    u3x31X₂ z * u3x31X₂i z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![4 + 1 * z, -3 + 2 * z, 9 + 13 * z; -7 + -6 * z, 5, 14 + 6 * z;
      -6 + -7 * z, -4 + -3 * z, -13 + -1 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![4 + -1 * z, -7 + 6 * z, -6 + 7 * z; -3 + -2 * z, 5, -4 + 3 * z;
        9 + -13 * z, 14 + -6 * z, -13 + 1 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-174) * hz + (9) * hp)
    (by linear_combination (-72) * hz + (5 + 5 * z) * hp)
    (by linear_combination (26) * hz + (-5 + -5 * z) * hp)
    (by linear_combination (-72) * hz + (5 + -5 * z) * hp)
    (by linear_combination (-72) * hz + (11) * hp)
    (by linear_combination (-36) * hz + (-4 + -2 * z) * hp)
    (by linear_combination (26) * hz + (-5 + 5 * z) * hp)
    (by linear_combination (-36) * hz + (-4 + 2 * z) * hp)
    (by linear_combination (-59) * hz + (9) * hp)

private theorem u3x31X₂i_mul (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    u3x31X₂i z * u3x31X₂ z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![4 + -1 * z, -7 + 6 * z, -6 + 7 * z; -3 + -2 * z, 5, -4 + 3 * z;
      9 + -13 * z, 14 + -6 * z, -13 + 1 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![4 + 1 * z, -3 + 2 * z, 9 + 13 * z; -7 + -6 * z, 5, 14 + 6 * z;
        -6 + -7 * z, -4 + -3 * z, -13 + -1 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-86) * hz + (6) * hp)
    (by linear_combination (-23) * hz + (1 * z) * hp)
    (by linear_combination (16) * hz)
    (by linear_combination (-23) * hz + (-1 * z) * hp)
    (by linear_combination (-13) * hz + (2) * hp)
    (by linear_combination (-29) * hz + (4 + -2 * z) * hp)
    (by linear_combination (16) * hz)
    (by linear_combination (-29) * hz + (4 + 2 * z) * hp)
    (by linear_combination (-206) * hz + (21) * hp)

private theorem u3x31Yf_mul (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    u3x31Yf z * u3x31Yfi z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![-5, 3 + 1 * z, 9 + -3 * z; 3 + 1 * z, -9 + 1 * z, 8;
      9 + -3 * z, 8, 6 + 11 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![-5, 3 + -1 * z, 9 + 3 * z; 3 + -1 * z, -9 + -1 * z, 8;
        9 + 3 * z, 8, 6 + -11 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-10) * hz + (4) * hp)
    (by linear_combination (-1) * hz + (1 + -1 * z) * hp)
    (by linear_combination (33) * hz + (-4 * z) * hp)
    (by linear_combination (-1) * hz + (1 + 1 * z) * hp)
    (by linear_combination (-2) * hz + (5) * hp)
    (by linear_combination (3) * hz + (-2 * z) * hp)
    (by linear_combination (33) * hz + (4 * z) * hp)
    (by linear_combination (3) * hz + (2 * z) * hp)
    (by linear_combination (-130) * hz + (10) * hp)

private theorem u3x31Yfi_mul (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    u3x31Yfi z * u3x31Yf z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![-5, 3 + -1 * z, 9 + 3 * z; 3 + -1 * z, -9 + -1 * z, 8;
      9 + 3 * z, 8, 6 + -11 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![-5, 3 + 1 * z, 9 + -3 * z; 3 + 1 * z, -9 + 1 * z, 8;
        9 + -3 * z, 8, 6 + 11 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-10) * hz + (4) * hp)
    (by linear_combination (-1) * hz + (1 + 1 * z) * hp)
    (by linear_combination (33) * hz + (4 * z) * hp)
    (by linear_combination (-1) * hz + (1 + -1 * z) * hp)
    (by linear_combination (-2) * hz + (5) * hp)
    (by linear_combination (3) * hz + (2 * z) * hp)
    (by linear_combination (33) * hz + (-4 * z) * hp)
    (by linear_combination (3) * hz + (-2 * z) * hp)
    (by linear_combination (-130) * hz + (10) * hp)

private theorem det_u3x31X₁ (hp : (31 : K) = 0) (hz : z ^ 2 = -1) : (u3x31X₁ z).det = 1 := by
  rw [show u3x31X₁ z = !![-6 + -8 * z, 1 + 4 * z, 15; -5 + 2 * z, 3, 3 + -4 * z;
      5 + -8 * z, 6 + 1 * z, -5 + 6 * z] from rfl, det3_of]
  linear_combination (-302 + 48 * z) * hz + (-6 + 13 * z) * hp

private theorem det_u3x31X₂ (hp : (31 : K) = 0) (hz : z ^ 2 = -1) : (u3x31X₂ z).det = 1 := by
  rw [show u3x31X₂ z = !![4 + 1 * z, -3 + 2 * z, 9 + 13 * z; -7 + -6 * z, 5, 14 + 6 * z;
      -6 + -7 * z, -4 + -3 * z, -13 + -1 * z] from rfl, det3_of]
  linear_combination (1041 + 156 * z) * hz + (-1 + 60 * z) * hp

private theorem det_u3x31Yf (hp : (31 : K) = 0) (hz : z ^ 2 = -1) : (u3x31Yf z).det = 1 := by
  rw [show u3x31Yf z = !![-5, 3 + 1 * z, 9 + -3 * z; 3 + 1 * z, -9 + 1 * z, 8;
      9 + -3 * z, 8, 6 + 11 * z] from rfl, det3_of]
  linear_combination (-40 + -20 * z) * hz + (56 + -7 * z) * hp

private theorem map_u3x31X₁ (σ : K →+* K) (hσ : σ z = -z) :
    (u3x31X₁ z).map σ = (u3x31X₁i z)ᵀ := by
  rw [show u3x31X₁ z = !![-6 + -8 * z, 1 + 4 * z, 15; -5 + 2 * z, 3, 3 + -4 * z;
      5 + -8 * z, 6 + 1 * z, -5 + 6 * z] from rfl, map_fin_three_of]
  rw [show (u3x31X₁i z)ᵀ = !![-6 + 8 * z, 1 + -4 * z, 15; -5 + -2 * z, 3, 3 + 4 * z;
      5 + 8 * z, 6 + -1 * z, -5 + -6 * z] by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl]
  exact mat3_congr
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)

private theorem map_u3x31X₂ (σ : K →+* K) (hσ : σ z = -z) :
    (u3x31X₂ z).map σ = (u3x31X₂i z)ᵀ := by
  rw [show u3x31X₂ z = !![4 + 1 * z, -3 + 2 * z, 9 + 13 * z; -7 + -6 * z, 5, 14 + 6 * z;
      -6 + -7 * z, -4 + -3 * z, -13 + -1 * z] from rfl, map_fin_three_of]
  rw [show (u3x31X₂i z)ᵀ = !![4 + -1 * z, -3 + -2 * z, 9 + -13 * z; -7 + 6 * z, 5, 14 + -6 * z;
      -6 + 7 * z, -4 + 3 * z, -13 + 1 * z] by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl]
  exact mat3_congr
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)

private theorem map_u3x31Yf (σ : K →+* K) (hσ : σ z = -z) :
    (u3x31Yf z).map σ = (u3x31Yfi z)ᵀ := by
  rw [show u3x31Yf z = !![-5, 3 + 1 * z, 9 + -3 * z; 3 + 1 * z, -9 + 1 * z, 8;
      9 + -3 * z, 8, 6 + 11 * z] from rfl, map_fin_three_of]
  rw [show (u3x31Yfi z)ᵀ = !![-5, 3 + -1 * z, 9 + 3 * z; 3 + -1 * z, -9 + -1 * z, 8;
      9 + 3 * z, 8, 6 + -11 * z] by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl]
  exact mat3_congr
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)

private theorem transpose_u3x31Yf : (u3x31Yf z)ᵀ = u3x31Yf z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem u3x31_w2 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![-6 + -8 * z, 1 + 4 * z, 15; -5 + 2 * z, 3, 3 + -4 * z; 5 + -8 * z, 6 + 1 * z, -5 + 6 * z] =
      !![6 + 8 * z, -1 + -4 * z, -15;
         5 + -2 * z, -3, -3 + 4 * z;
         5 + -8 * z, 6 + 1 * z, -5 + 6 * z] := by
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

private theorem u3x31_w3 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![6 + 8 * z, -1 + -4 * z, -15;
        5 + -2 * z, -3, -3 + 4 * z;
        5 + -8 * z, 6 + 1 * z, -5 + 6 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      !![-6 + -8 * z, 1 + 4 * z, -15;
         -5 + 2 * z, 3, -3 + 4 * z;
         -5 + 8 * z, -6 + -1 * z, -5 + 6 * z] := by
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

private theorem u3x31_w4 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-6 + -8 * z, 1 + 4 * z, -15;
        -5 + 2 * z, 3, -3 + 4 * z;
        -5 + 8 * z, -6 + -1 * z, -5 + 6 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-6 + 8 * z, -5 + -2 * z, 5 + 8 * z;
         1 + -4 * z, 3, 6 + -1 * z;
         15, 3 + 4 * z, -5 + -6 * z] =
      !![-15, 3 + 4 * z, -5 + -6 * z;
         3 + -4 * z, 13, -15 + -4 * z;
         5 + -6 * z, 15 + -4 * z, -3] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-80) * hz + (-3) * hp)
    (by linear_combination (16) * hz + (-1) * hp)
    (by linear_combination (-68) * hz + (4 + 1 * z) * hp)
    (by linear_combination (16) * hz + (-1) * hp)
    (by linear_combination (12) * hz)
    (by linear_combination (-8) * hz + (1 + -1 * z) * hp)
    (by linear_combination (68) * hz + (-4 + 1 * z) * hp)
    (by linear_combination (8) * hz + (-1 + -1 * z) * hp)
    (by linear_combination (29) * hz + (-2) * hp)

private theorem u3x31_w5 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-15, 3 + 4 * z, -5 + -6 * z;
        3 + -4 * z, 13, -15 + -4 * z;
        5 + -6 * z, 15 + -4 * z, -3] : Matrix (Fin 3) (Fin 3) K) *
      !![4 + 1 * z, -3 + 2 * z, 9 + 13 * z;
         -7 + -6 * z, 5, 14 + 6 * z;
         -6 + -7 * z, -4 + -3 * z, -13 + -1 * z] =
      !![-7 + 10 * z, -2 * z, 4 + -7 * z;
         -13 + 7 * z, -12 + -14 * z, -13 + -7 * z;
         8 + 2 * z, -9 + -14 * z, -7 + -14 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (18) * hz + (-2) * hp)
    (by linear_combination (18) * hz + (2 + 1 * z) * hp)
    (by linear_combination (30) * hz + (-2 + -1 * z) * hp)
    (by linear_combination (24) * hz + (1 * z) * hp)
    (by linear_combination (4) * hz + (4 + 3 * z) * hp)
    (by linear_combination (-48) * hz + (15 + 5 * z) * hp)
    (by linear_combination (18) * hz + (-3 + -2 * z) * hp)
    (by linear_combination (-12) * hz + (3 + 1 * z) * hp)
    (by linear_combination (-102) * hz + (13 + 2 * z) * hp)

private theorem u3x31_w6 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-7 + 10 * z, -2 * z, 4 + -7 * z;
        -13 + 7 * z, -12 + -14 * z, -13 + -7 * z;
        8 + 2 * z, -9 + -14 * z, -7 + -14 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      !![7 + -10 * z, 2 * z, 4 + -7 * z;
         13 + -7 * z, 12 + 14 * z, -13 + -7 * z;
         -8 + -2 * z, 9 + 14 * z, -7 + -14 * z] := by
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

private theorem u3x31_w7 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![7 + -10 * z, 2 * z, 4 + -7 * z;
        13 + -7 * z, 12 + 14 * z, -13 + -7 * z;
        -8 + -2 * z, 9 + 14 * z, -7 + -14 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![4 + -1 * z, -7 + 6 * z, -6 + 7 * z;
         -3 + -2 * z, 5, -4 + 3 * z;
         9 + -13 * z, 14 + -6 * z, -13 + 1 * z] =
      !![-2 + -13 * z, -6, 8 + 10 * z;
         15 + -1 * z, 4 + -9 * z, -5 + 5 * z;
         1 + -2 * z, -7 + 6 * z, -4 + 9 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (97) * hz + (-1 + -5 * z) * hp)
    (by linear_combination (-18) * hz + (1) * hp)
    (by linear_combination (-71) * hz + (-1 + 6 * z) * hp)
    (by linear_combination (70) * hz + (-6) * hp)
    (by linear_combination (-7 + 6 * z) * hp)
    (by linear_combination (-14) * hz + (2 + 6 * z) * hp)
    (by linear_combination (156) * hz + (-9 + -3 * z) * hp)
    (by linear_combination (72) * hz + (-2 + -4 * z) * hp)
    (by linear_combination (14) * hz + (3 + 3 * z) * hp)

private theorem u3x31_word (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * u3x31X₁ z * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * u3x31X₁i z *
      u3x31X₂ z * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * u3x31X₂i z = u3x31Y z := by
  rw [show u3x31X₁ z = !![-6 + -8 * z, 1 + 4 * z, 15; -5 + 2 * z, 3, 3 + -4 * z;
      5 + -8 * z, 6 + 1 * z, -5 + 6 * z] from rfl,
    show u3x31X₁i z = !![-6 + 8 * z, -5 + -2 * z, 5 + 8 * z; 1 + -4 * z, 3, 6 + -1 * z;
        15, 3 + 4 * z, -5 + -6 * z] from rfl,
    show u3x31X₂ z = !![4 + 1 * z, -3 + 2 * z, 9 + 13 * z; -7 + -6 * z, 5, 14 + 6 * z;
        -6 + -7 * z, -4 + -3 * z, -13 + -1 * z] from rfl,
    show u3x31X₂i z = !![4 + -1 * z, -7 + 6 * z, -6 + 7 * z; -3 + -2 * z, 5, -4 + 3 * z;
        9 + -13 * z, 14 + -6 * z, -13 + 1 * z] from rfl]
  rw [u3x31_w2 hp hz, u3x31_w3 hp hz, u3x31_w4 hp hz, u3x31_w5 hp hz, u3x31_w6 hp hz,
      u3x31_w7 hp hz]
  rfl

private theorem u3x31Y_sq2 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-2 + -13 * z, -6, 8 + 10 * z;
        15 + -1 * z, 4 + -9 * z, -5 + 5 * z;
        1 + -2 * z, -7 + 6 * z, -4 + 9 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-2 + -13 * z, -6, 8 + 10 * z;
         15 + -1 * z, 4 + -9 * z, -5 + 5 * z;
         1 + -2 * z, -7 + 6 * z, -4 + 9 * z] =
      !![-10 + -10 * z, -4 + -14 * z, -9 + 2 * z;
         13 + -7 * z, 5 + -7 * z, 6 + -13 * z;
         11 + 12 * z, -6 + 12 * z, -1 + 12 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (149) * hz + (-7 + 2 * z) * hp)
    (by linear_combination (60) * hz + (-4 + 4 * z) * hp)
    (by linear_combination (-40) * hz + (1 + -4 * z) * hp)
    (by linear_combination (12) * hz + (-10 * z) * hp)
    (by linear_combination (111) * hz + (-5 + -4 * z) * hp)
    (by linear_combination (-10) * hz + (4 + 5 * z) * hp)
    (by linear_combination (2) * hz + (-4 + 3 * z) * hp)
    (by linear_combination)
    (by linear_combination (91) * hz + (-1 + -5 * z) * hp)

private theorem u3x31Y_sq4 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-10 + -10 * z, -4 + -14 * z, -9 + 2 * z;
        13 + -7 * z, 5 + -7 * z, 6 + -13 * z;
        11 + 12 * z, -6 + 12 * z, -1 + 12 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-10 + -10 * z, -4 + -14 * z, -9 + 2 * z;
         13 + -7 * z, 5 + -7 * z, 6 + -13 * z;
         11 + 12 * z, -6 + 12 * z, -1 + 12 * z] =
      !![6 + -9 * z, -2 + -13 * z, 13 + -10 * z;
         7 + -9 * z, 8 + -12 * z, -14 + 5 * z;
         -15 + -5 * z, 9 + 2 * z, 9 + 9 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (222) * hz + (-9 + -1 * z) * hp)
    (by linear_combination (262) * hz + (-6 + 1 * z) * hp)
    (by linear_combination (186) * hz + (-4 + -2 * z) * hp)
    (by linear_combination (-37) * hz + (1 + -8 * z) * hp)
    (by linear_combination (-9) * hz + (-2 + -2 * z) * hp)
    (by linear_combination (-79) * hz + (2 * z) * hp)
    (by linear_combination (-60) * hz + (-4 + 3 * z) * hp)
    (by linear_combination (-108) * hz + (1 + -6 * z) * hp)
    (by linear_combination (12) * hz + (-5 + 1 * z) * hp)

private theorem u3x31Y_sq8 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![6 + -9 * z, -2 + -13 * z, 13 + -10 * z;
        7 + -9 * z, 8 + -12 * z, -14 + 5 * z;
        -15 + -5 * z, 9 + 2 * z, 9 + 9 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![6 + -9 * z, -2 + -13 * z, 13 + -10 * z;
         7 + -9 * z, 8 + -12 * z, -14 + 5 * z;
         -15 + -5 * z, 9 + 2 * z, 9 + 9 * z] =
      !![13 + -3 * z, -9 + 13 * z, 9 + -9 * z;
         -11 + 1 * z, -6, -5 + 2 * z;
         11 + 13 * z, -5 * z, -9 + -15 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (248) * hz + (-14 + -3 * z) * hp)
    (by linear_combination (253) * hz + (-5 + -7 * z) * hp)
    (by linear_combination (-65) * hz + (9 + 1 * z) * hp)
    (by linear_combination (164) * hz + (5 + -9 * z) * hp)
    (by linear_combination (271) * hz + (-11 + -8 * z) * hp)
    (by linear_combination (75) * hz + (-7 + -2 * z) * hp)
    (by linear_combination (-18) * hz + (-5 + -5 * z) * hp)
    (by linear_combination (59) * hz + (4 + 7 * z) * hp)
    (by linear_combination (141) * hz + (-12 + 9 * z) * hp)

private theorem u3x31Y_sq16 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![13 + -3 * z, -9 + 13 * z, 9 + -9 * z;
        -11 + 1 * z, -6, -5 + 2 * z;
        11 + 13 * z, -5 * z, -9 + -15 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![13 + -3 * z, -9 + 13 * z, 9 + -9 * z;
         -11 + 1 * z, -6, -5 + 2 * z;
         11 + 13 * z, -5 * z, -9 + -15 * z] =
      !![-3 + 5 * z, -7 + 11 * z, -14 + -2 * z;
         -3 * z, 8 + -3 * z, 15 + -2 * z;
         4 + 2 * z, -2 + 8 * z, -11 + 3 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-95) * hz + (15 + -7 * z) * hp)
    (by linear_combination (6) * hz + (-2 + 2 * z) * hp)
    (by linear_combination (188) * hz + (-3 + -9 * z) * hp)
    (by linear_combination (23) * hz + (-5) * hp)
    (by linear_combination (3) * hz + (4 + -4 * z) * hp)
    (by linear_combination (-39) * hz + (5 * z) * hp)
    (by linear_combination (-239) * hz + (9 + -3 * z) * hp)
    (by linear_combination (244) * hz + (-11 + 3 * z) * hp)
    (by linear_combination (98) * hz + (3 + 10 * z) * hp)

private theorem u3x31Y_q1 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-3 + 5 * z, -7 + 11 * z, -14 + -2 * z;
        -3 * z, 8 + -3 * z, 15 + -2 * z;
        4 + 2 * z, -2 + 8 * z, -11 + 3 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-10 + -10 * z, -4 + -14 * z, -9 + 2 * z;
         13 + -7 * z, 5 + -7 * z, 6 + -13 * z;
         11 + 12 * z, -6 + 12 * z, -1 + 12 * z] =
      !![-2 + 13 * z, 15 + 1 * z, 1 + 2 * z;
         -6, 4 + 9 * z, -7 + -6 * z;
         8 + -10 * z, -5 + -5 * z, -4 + -9 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-151) * hz + (-2 + -1 * z) * hp)
    (by linear_combination (-171) * hz + (7 + -1 * z) * hp)
    (by linear_combination (-157) * hz + (5 + -2 * z) * hp)
    (by linear_combination (27) * hz + (8 + 3 * z) * hp)
    (by linear_combination (39) * hz + (-3 + 4 * z) * hp)
    (by linear_combination (9) * hz + (1 + 3 * z) * hp)
    (by linear_combination (-40) * hz + (-5 + -1 * z) * hp)
    (by linear_combination (-48) * hz + (3 + -5 * z) * hp)
    (by linear_combination (-64) * hz + (1 + -2 * z) * hp)

private theorem u3x31Y_q2 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-2 + 13 * z, 15 + 1 * z, 1 + 2 * z;
        -6, 4 + 9 * z, -7 + -6 * z;
        8 + -10 * z, -5 + -5 * z, -4 + -9 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-2 + -13 * z, -6, 8 + 10 * z;
         15 + -1 * z, 4 + -9 * z, -5 + 5 * z;
         1 + -2 * z, -7 + 6 * z, -4 + 9 * z] =
      !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-174) * hz + (13) * hp)
    (by linear_combination (3) * hz + (2 + -7 * z) * hp)
    (by linear_combination (153) * hz + (-8 + 5 * z) * hp)
    (by linear_combination (3) * hz + (2 + 7 * z) * hp)
    (by linear_combination (-117) * hz + (7) * hp)
    (by linear_combination (-9) * hz + (-1 + -4 * z) * hp)
    (by linear_combination (153) * hz + (-8 + -5 * z) * hp)
    (by linear_combination (-9) * hz + (-1 + 4 * z) * hp)
    (by linear_combination (-206) * hz + (10) * hp)

private theorem u3x31Y_pow (hp : (31 : K) = 0) (hz : z ^ 2 = -1) : u3x31Y z ^ 19 = 1 := by
  show (!![-2 + -13 * z, -6, 8 + 10 * z; 15 + -1 * z, 4 + -9 * z, -5 + 5 * z;
      1 + -2 * z, -7 + 6 * z, -4 + 9 * z] : Matrix (Fin 3) (Fin 3) K) ^ 19 = 1
  refine pow_eq_one_of_sq_chain_19_31
    (u3x31Y_sq2 hp hz)
    (u3x31Y_sq4 hp hz)
    (u3x31Y_sq8 hp hz)
    (u3x31Y_sq16 hp hz) ?_
  rw [u3x31Y_q1 hp hz, u3x31Y_q2 hp hz]
  exact Matrix.one_fin_three.symm

private theorem u3x31Yf_sq2 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-5, 3 + 1 * z, 9 + -3 * z;
        3 + 1 * z, -9 + 1 * z, 8;
        9 + -3 * z, 8, 6 + 11 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-5, 3 + 1 * z, 9 + -3 * z; 3 + 1 * z, -9 + 1 * z, 8; 9 + -3 * z, 8, 6 + 11 * z] =
      !![12 + 14 * z, -2 + -4 * z, 4 + 11 * z;
         -2 + -4 * z, -3 + -12 * z, 6 + 3 * z;
         4 + 11 * z, 6 + 3 * z, -11 + -15 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (10) * hz + (3 + -2 * z) * hp)
    (by linear_combination (1) * hz + (1 + -1 * z) * hp)
    (by linear_combination (-33) * hz + (2 + 3 * z) * hp)
    (by linear_combination (1) * hz + (1 + -1 * z) * hp)
    (by linear_combination (2) * hz + (5) * hp)
    (by linear_combination (-3) * hz + (3 * z) * hp)
    (by linear_combination (-33) * hz + (2 + 3 * z) * hp)
    (by linear_combination (-3) * hz + (3 * z) * hp)
    (by linear_combination (130) * hz + (2 + 3 * z) * hp)

private theorem u3x31Yf_sq4 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![12 + 14 * z, -2 + -4 * z, 4 + 11 * z;
        -2 + -4 * z, -3 + -12 * z, 6 + 3 * z;
        4 + 11 * z, 6 + 3 * z, -11 + -15 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![12 + 14 * z, -2 + -4 * z, 4 + 11 * z;
         -2 + -4 * z, -3 + -12 * z, 6 + 3 * z;
         4 + 11 * z, 6 + 3 * z, -11 + -15 * z] =
      !![-14 + 6 * z, 12 + 7 * z, 15 + 8 * z;
         12 + 7 * z, 4, 2 + 6 * z;
         15 + 8 * z, 2 + 6 * z, 4 + -11 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (333) * hz + (-5 + 14 * z) * hp)
    (by linear_combination (25) * hz + (-1 + 1 * z) * hp)
    (by linear_combination (-23) * hz + (-1 * z) * hp)
    (by linear_combination (25) * hz + (-1 + 1 * z) * hp)
    (by linear_combination (169) * hz + (-4 + 4 * z) * hp)
    (by linear_combination (-125) * hz + (1 + -8 * z) * hp)
    (by linear_combination (-23) * hz + (-1 * z) * hp)
    (by linear_combination (-125) * hz + (1 + -8 * z) * hp)
    (by linear_combination (355) * hz + (-6 + 15 * z) * hp)

private theorem u3x31Yf_sq8 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-14 + 6 * z, 12 + 7 * z, 15 + 8 * z;
        12 + 7 * z, 4, 2 + 6 * z;
        15 + 8 * z, 2 + 6 * z, 4 + -11 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-14 + 6 * z, 12 + 7 * z, 15 + 8 * z;
         12 + 7 * z, 4, 2 + 6 * z;
         15 + 8 * z, 2 + 6 * z, 4 + -11 * z] =
      !![13 + -8 * z, 6 + 15 * z, -4 + -7 * z;
         6 + 15 * z, -14 + 6 * z, -11 + 10 * z;
         -4 + -7 * z, -11 + 10 * z, -7 + -10 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (149) * hz + (13 + 8 * z) * hp)
    (by linear_combination (90) * hz + (-6 + 3 * z) * hp)
    (by linear_combination (2) * hz + (-4 + -2 * z) * hp)
    (by linear_combination (90) * hz + (-6 + 3 * z) * hp)
    (by linear_combination (85) * hz + (3 + 6 * z) * hp)
    (by linear_combination (-10) * hz + (7 + 7 * z) * hp)
    (by linear_combination (2) * hz + (-4 + -2 * z) * hp)
    (by linear_combination (-10) * hz + (7 + 7 * z) * hp)
    (by linear_combination (221) * hz + (1 + 6 * z) * hp)

private theorem u3x31Yf_sq16 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![13 + -8 * z, 6 + 15 * z, -4 + -7 * z;
        6 + 15 * z, -14 + 6 * z, -11 + 10 * z;
        -4 + -7 * z, -11 + 10 * z, -7 + -10 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![13 + -8 * z, 6 + 15 * z, -4 + -7 * z;
         6 + 15 * z, -14 + 6 * z, -11 + 10 * z;
         -4 + -7 * z, -11 + 10 * z, -7 + -10 * z] =
      !![7 + -3 * z, 14 + 10 * z, 6 + -13 * z;
         14 + 10 * z, -8 + 9 * z, 11 + 11 * z;
         6 + -13 * z, 11 + 11 * z, -1 + 7 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (338) * hz + (-4 + 1 * z) * hp)
    (by linear_combination (-100) * hz + (4) * hp)
    (by linear_combination (276) * hz + (-12 + -2 * z) * hp)
    (by linear_combination (-100) * hz + (4) * hp)
    (by linear_combination (361) * hz + (-7 * z) * hp)
    (by linear_combination (-145) * hz + (11 + -9 * z) * hp)
    (by linear_combination (276) * hz + (-12 + -2 * z) * hp)
    (by linear_combination (-145) * hz + (11 + -9 * z) * hp)
    (by linear_combination (249) * hz + (-2 + -1 * z) * hp)

private theorem u3x31Yf_q1 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![7 + -3 * z, 14 + 10 * z, 6 + -13 * z;
        14 + 10 * z, -8 + 9 * z, 11 + 11 * z;
        6 + -13 * z, 11 + 11 * z, -1 + 7 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![12 + 14 * z, -2 + -4 * z, 4 + 11 * z;
         -2 + -4 * z, -3 + -12 * z, 6 + 3 * z;
         4 + 11 * z, 6 + 3 * z, -11 + -15 * z] =
      !![-5, 3 + -1 * z, 9 + 3 * z; 3 + -1 * z, -9 + -1 * z, 8; 9 + 3 * z, 8, 6 + -11 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-225) * hz + (10) * hp)
    (by linear_combination (-147) * hz + (4 + -9 * z) * hp)
    (by linear_combination (192) * hz + (-5 + 7 * z) * hp)
    (by linear_combination (225) * hz + (16 * z) * hp)
    (by linear_combination (-115) * hz + (6 + 3 * z) * hp)
    (by linear_combination (-28) * hz + (-3 + -2 * z) * hp)
    (by linear_combination (-149) * hz + (6 + -4 * z) * hp)
    (by linear_combination (-59) * hz + (-4 * z) * hp)
    (by linear_combination (-215) * hz + (10 + 2 * z) * hp)

private theorem u3x31Yf_q2 (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-5, 3 + -1 * z, 9 + 3 * z;
        3 + -1 * z, -9 + -1 * z, 8;
        9 + 3 * z, 8, 6 + -11 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-5, 3 + 1 * z, 9 + -3 * z; 3 + 1 * z, -9 + 1 * z, 8; 9 + -3 * z, 8, 6 + 11 * z] =
      !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-10) * hz + (4) * hp)
    (by linear_combination (-1) * hz + (1 + 1 * z) * hp)
    (by linear_combination (33) * hz + (4 * z) * hp)
    (by linear_combination (-1) * hz + (1 + -1 * z) * hp)
    (by linear_combination (-2) * hz + (5) * hp)
    (by linear_combination (3) * hz + (2 * z) * hp)
    (by linear_combination (33) * hz + (-4 * z) * hp)
    (by linear_combination (3) * hz + (-2 * z) * hp)
    (by linear_combination (-130) * hz + (10) * hp)

private theorem u3x31Yf_pow (hp : (31 : K) = 0) (hz : z ^ 2 = -1) : u3x31Yf z ^ 19 = 1 := by
  show (!![-5, 3 + 1 * z, 9 + -3 * z; 3 + 1 * z, -9 + 1 * z, 8;
      9 + -3 * z, 8, 6 + 11 * z] : Matrix (Fin 3) (Fin 3) K) ^ 19 = 1
  refine pow_eq_one_of_sq_chain_19_31
    (u3x31Yf_sq2 hp hz)
    (u3x31Yf_sq4 hp hz)
    (u3x31Yf_sq8 hp hz)
    (u3x31Yf_sq16 hp hz) ?_
  rw [u3x31Yf_q1 hp hz, u3x31Yf_q2 hp hz]
  exact Matrix.one_fin_three.symm

private theorem u3x31Y_ne_one (hp : (31 : K) = 0) (hz : z ^ 2 = -1) : u3x31Y z ≠ 1 := by
  intro h1
  have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 1) h1
  simp [u3x31Y] at e
  exact one_ne_zero (α := K) (by linear_combination (-5) * e + (1) * hp)

private theorem u3x31Yf_ne_one (hp : (31 : K) = 0) (hz : z ^ 2 = -1) : u3x31Yf z ≠ 1 := by
  intro h1
  have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 2) h1
  simp [u3x31Yf] at e
  exact one_ne_zero (α := K) (by linear_combination (4) * e + (-1) * hp)

end Words

section Group

variable {K : Type} [Field K]

private theorem negNegOneDiag_eq_u3x31 :
    negNegOneDiag K = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negNegOneDiag]

private def u3x31X₁SU (h : UnitaryFieldData 31 1 K) {z : K}
    (hp : (31 : K) = 0) (hz : z ^ 2 = -1) (hbar : h.bar z = -z) : unitarySU 31 1 K 3 :=
  ⟨⟨u3x31X₁ z, u3x31X₁i z, u3x31X₁_mul hp hz, u3x31X₁i_mul hp hz⟩,
    (mem_unitarySU_iff h).mpr ⟨det_u3x31X₁ hp hz, by
      change ((u3x31X₁ z).map h.bar)ᵀ * u3x31X₁ z = 1
      rw [map_u3x31X₁ h.bar hbar, Matrix.transpose_transpose, u3x31X₁i_mul hp hz]⟩⟩

private def u3x31X₂SU (h : UnitaryFieldData 31 1 K) {z : K}
    (hp : (31 : K) = 0) (hz : z ^ 2 = -1) (hbar : h.bar z = -z) : unitarySU 31 1 K 3 :=
  ⟨⟨u3x31X₂ z, u3x31X₂i z, u3x31X₂_mul hp hz, u3x31X₂i_mul hp hz⟩,
    (mem_unitarySU_iff h).mpr ⟨det_u3x31X₂ hp hz, by
      change ((u3x31X₂ z).map h.bar)ᵀ * u3x31X₂ z = 1
      rw [map_u3x31X₂ h.bar hbar, Matrix.transpose_transpose, u3x31X₂i_mul hp hz]⟩⟩

private theorem excl1412_conj_U3_31 (h : UnitaryFieldData 31 1 K) {z : K}
    (hp : (31 : K) = 0) (hz : z ^ 2 = -1) (hbar : h.bar z = -z) :
    Excl1412 (MulAut.conj (unitaryProj h 3 (unitaryInvT h))) := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  set x₁ := u3x31X₁SU h hp hz hbar with hx₁def
  set x₂ := u3x31X₂SU h hp hz hbar with hx₂def
  set τ := unitaryProj h 3 (unitaryInvT h) with hτdef
  have hτ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by
    rw [hτdef, ← map_mul, ← sq, unitaryInvT_sq, map_one])
  set y : unitarySU 31 1 K 3 :=
    unitaryInvT h * x₁ * unitaryInvT h * x₁⁻¹ * x₂ * unitaryInvT h * x₂⁻¹ with hydef
  have hy : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u3x31Y z := by
    rw [hydef, ← u3x31_word hp hz, ← negNegOneDiag_eq_u3x31, ← coe_unitaryInvT h]
    rfl
  have hyo : orderOf (unitaryProj h 3 y) = 19 := by
    rw [orderOf_injective _ (unitaryProj_injective_exc h (by norm_num)) y, ← Subgroup.orderOf_coe,
      ← orderOf_units, hy]
    exact orderOf_eq_prime (u3x31Y_pow hp hz) (u3x31Y_ne_one hp hz)
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
  refine Or.inr (Or.inl ⟨unitaryProj h 3 x₁, unitaryProj h 3 x₂, a * b⁻¹ * a⁻¹ * b, 19, 1,
    by norm_num, by norm_num, le_rfl, fun e he1 he12 => by
      interval_cases e <;> norm_num,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb))
      (Subgroup.inv_mem _ ha)) hb, ?_⟩)
  rw [pow_one, hw, Nat.Coprime.orderOf_pow (by rw [hyo]; norm_num), hyo]

private def u3x31YfGL {z : K} (hp : (31 : K) = 0) (hz : z ^ 2 = -1) : GL (Fin 3) K :=
  ⟨u3x31Yf z, u3x31Yfi z, u3x31Yf_mul hp hz, u3x31Yfi_mul hp hz⟩

private theorem u3x31YfGL_mem (h : UnitaryFieldData 31 1 K) {z : K}
    (hp : (31 : K) = 0) (hz : z ^ 2 = -1) (hbar : h.bar z =
        -z) : u3x31YfGL hp hz ∈ unitarySU 31 1 K 3 :=
  (mem_unitarySU_iff h).mpr ⟨det_u3x31Yf hp hz, by
    change ((u3x31Yf z).map h.bar)ᵀ * u3x31Yf z = 1
    rw [map_u3x31Yf h.bar hbar, Matrix.transpose_transpose, u3x31Yfi_mul hp hz]⟩

private theorem orderOf_u3x31YfGL {z : K} (hp : (31 : K) = 0) (hz : z ^ 2 = -1) :
    orderOf (u3x31YfGL hp hz) = 19 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  rw [← orderOf_units]
  exact orderOf_eq_prime (u3x31Yf_pow hp hz) (u3x31Yf_ne_one hp hz)

end Group

theorem excl1412_U3_31 (K : Type) [Field K] (h : UnitaryFieldData 31 1 K)
    (α : MulAut (unitaryPSU h 3)) (hα : orderOf α = 2) : Excl1412 α := by
  obtain ⟨hp, z, hz, hbar⟩ := exists_sq_eq_neg_one_of_unitary_exc h (by norm_num)
  have hp' : (31 : K) = 0 := by exact_mod_cast hp
  exact excl1412_unitaryPSU3_of_exc h (by norm_num) (excl1412_conj_U3_31 h hp' hz hbar)
    (u3x31YfGL_mem h hp' hz hbar) transpose_u3x31Yf (q := 19) (k := 1) (by norm_num)
    (by norm_num) le_rfl (fun e he1 he8 => by interval_cases e <;> norm_num)
    (by rw [pow_one, orderOf_u3x31YfGL]) α hα

end CFSG.RankThree.PartTwo.Sec20

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

private theorem pow_eq_one_of_sq_chain_1231_127 {G : Type*} [Monoid G]
    {m s2 s4 s8 s16 s32 s64 s128 s256 s512 s1024 : G}
    (h2 : m * m = s2) (h4 : s2 * s2 = s4) (h8 : s4 * s4 = s8) (h16 : s8 * s8 = s16)
    (h32 : s16 * s16 = s32) (h64 : s32 * s32 = s64) (h128 : s64 * s64 = s128)
    (h256 : s128 * s128 = s256) (h512 : s256 * s256 = s512) (h1024 : s512 * s512 = s1024)
    (h : s1024 * s128 * s64 * s8 * s4 * s2 * m = 1) :
    m ^ 1231 = 1 := by
  have e2 : s2 = m ^ 2 := by rw [← h2, sq]
  have e4 : s4 = m ^ 4 := by rw [← h4, e2, ← pow_add]
  have e8 : s8 = m ^ 8 := by rw [← h8, e4, ← pow_add]
  have e16 : s16 = m ^ 16 := by rw [← h16, e8, ← pow_add]
  have e32 : s32 = m ^ 32 := by rw [← h32, e16, ← pow_add]
  have e64 : s64 = m ^ 64 := by rw [← h64, e32, ← pow_add]
  have e128 : s128 = m ^ 128 := by rw [← h128, e64, ← pow_add]
  have e256 : s256 = m ^ 256 := by rw [← h256, e128, ← pow_add]
  have e512 : s512 = m ^ 512 := by rw [← h512, e256, ← pow_add]
  have e1024 : s1024 = m ^ 1024 := by rw [← h1024, e512, ← pow_add]
  rw [← h, e1024, e128, e64, e8, e4, e2, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_succ]

private theorem pow_eq_one_of_sq_chain_13_127 {G : Type*} [Monoid G] {m s2 s4 s8 : G}
    (h2 : m * m = s2) (h4 : s2 * s2 = s4) (h8 : s4 * s4 = s8) (h : s8 * s4 * m = 1) :
    m ^ 13 = 1 := by
  have e2 : s2 = m ^ 2 := by rw [← h2, sq]
  have e4 : s4 = m ^ 4 := by rw [← h4, e2, ← pow_add]
  have e8 : s8 = m ^ 8 := by rw [← h8, e4, ← pow_add]
  rw [← h, e8, e4, ← pow_add, ← pow_succ]

private def u3x127X₁ (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6 + 15 * z, -49 + -16 * z, 7 + 35 * z; 43 + -10 * z, -7 + 48 * z, 4 + 1 * z;
      25 + -50 * z, 7 + 28 * z, -19]

private def u3x127X₁i (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![6 + -15 * z, 43 + 10 * z, 25 + 50 * z; -49 + 16 * z, -7 + -48 * z, 7 + -28 * z;
      7 + -35 * z, 4 + -1 * z, -19]

private def u3x127X₂ (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![23 + 31 * z, -1 + -28 * z, 54 + -12 * z; -1 + -20 * z, -2 + -56 * z, 4;
      14 + 33 * z, -5 + 49 * z, -37 + 1 * z]

private def u3x127X₂i (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![23 + -31 * z, -1 + 20 * z, 14 + -33 * z; -1 + 28 * z, -2 + 56 * z, -5 + -49 * z;
      54 + 12 * z, 4, -37 + -1 * z]

private def u3x127Y (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![-17 + 3 * z, -40 + 35 * z, 37 + -9 * z; -3 + -19 * z, -31 + 9 * z, -34 + -10 * z;
      -18 + 5 * z, -1 + -18 * z, -31 + 12 * z]

private def u3x127Yf (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![30 + -5 * z, 11 + 10 * z, -11 + 2 * z; 11 + 10 * z, -50 + -14 * z, 30 + -11 * z;
      -11 + 2 * z, 30 + -11 * z, 60 + 9 * z]

private def u3x127Yfi (z : K) : Matrix (Fin 3) (Fin 3) K :=
  !![30 + 5 * z, 11 + -10 * z, -11 + -2 * z; 11 + -10 * z, -50 + 14 * z, 30 + 11 * z;
      -11 + -2 * z, 30 + 11 * z, 60 + -9 * z]

private theorem u3x127X₁_mul (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    u3x127X₁ z * u3x127X₁i z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![6 + 15 * z, -49 + -16 * z, 7 + 35 * z; 43 + -10 * z, -7 + 48 * z, 4 + 1 * z;
      25 + -50 * z, 7 + 28 * z, -19] : Matrix (Fin 3) (Fin 3) K) *
    !![6 + -15 * z, 43 + 10 * z, 25 + 50 * z; -49 + 16 * z, -7 + -48 * z, 7 + -28 * z;
        7 + -35 * z, 4 + -1 * z, -19] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-1706) * hz + (33) * hp)
    (by linear_combination (883) * hz + (-2 + 26 * z) * hp)
    (by linear_combination (1198) * hz + (-12 + 10 * z) * hp)
    (by linear_combination (883) * hz + (-2 + -26 * z) * hp)
    (by linear_combination (-2405) * hz + (34) * hp)
    (by linear_combination (-1844) * hz + (22 + 19 * z) * hp)
    (by linear_combination (1198) * hz + (-12 + -10 * z) * hp)
    (by linear_combination (-1844) * hz + (22 + -19 * z) * hp)
    (by linear_combination (-3284) * hz + (34) * hp)

private theorem u3x127X₁i_mul (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    u3x127X₁i z * u3x127X₁ z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![6 + -15 * z, 43 + 10 * z, 25 + 50 * z; -49 + 16 * z, -7 + -48 * z, 7 + -28 * z;
      7 + -35 * z, 4 + -1 * z, -19] : Matrix (Fin 3) (Fin 3) K) *
    !![6 + 15 * z, -49 + -16 * z, 7 + 35 * z; 43 + -10 * z, -7 + 48 * z, 4 + 1 * z;
        25 + -50 * z, 7 + 28 * z, -19] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-2825) * hz + (42) * hp)
    (by linear_combination (2120) * hz + (-20 + 29 * z) * hp)
    (by linear_combination (-515) * hz + (2 + -6 * z) * hp)
    (by linear_combination (2120) * hz + (-20 + -29 * z) * hp)
    (by linear_combination (-3344) * hz + (46) * hp)
    (by linear_combination (512) * hz + (-8 + -10 * z) * hp)
    (by linear_combination (-515) * hz + (2 + 6 * z) * hp)
    (by linear_combination (512) * hz + (-8 + 10 * z) * hp)
    (by linear_combination (-1226) * hz + (13) * hp)

private theorem u3x127X₂_mul (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    u3x127X₂ z * u3x127X₂i z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![23 + 31 * z, -1 + -28 * z, 54 + -12 * z; -1 + -20 * z, -2 + -56 * z, 4;
      14 + 33 * z, -5 + 49 * z, -37 + 1 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![23 + -31 * z, -1 + 20 * z, 14 + -33 * z; -1 + 28 * z, -2 + 56 * z, -5 + -49 * z;
        54 + 12 * z, 4, -37 + -1 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-1889) * hz + (42) * hp)
    (by linear_combination (-948) * hz + (9 + 3 * z) * hp)
    (by linear_combination (361) * hz + (-16 + 2 * z) * hp)
    (by linear_combination (-948) * hz + (9 + -3 * z) * hp)
    (by linear_combination (-3536) * hz + (28) * hp)
    (by linear_combination (3404) * hz + (-28 + 1 * z) * hp)
    (by linear_combination (361) * hz + (-16 + -2 * z) * hp)
    (by linear_combination (3404) * hz + (-28 + -1 * z) * hp)
    (by linear_combination (-3491) * hz + (40) * hp)

private theorem u3x127X₂i_mul (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    u3x127X₂i z * u3x127X₂ z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![23 + -31 * z, -1 + 20 * z, 14 + -33 * z; -1 + 28 * z, -2 + 56 * z, -5 + -49 * z;
      54 + 12 * z, 4, -37 + -1 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![23 + 31 * z, -1 + -28 * z, 54 + -12 * z; -1 + -20 * z, -2 + -56 * z, 4;
        14 + 33 * z, -5 + 49 * z, -37 + 1 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-2450) * hz + (25) * hp)
    (by linear_combination (-1869) * hz + (14 + 2 * z) * hp)
    (by linear_combination (339) * hz + (3 + -5 * z) * hp)
    (by linear_combination (-1869) * hz + (14 + -2 * z) * hp)
    (by linear_combination (-6321) * hz + (50) * hp)
    (by linear_combination (-385) * hz + (4 + 28 * z) * hp)
    (by linear_combination (339) * hz + (3 + 5 * z) * hp)
    (by linear_combination (-385) * hz + (4 + -28 * z) * hp)
    (by linear_combination (-145) * hz + (35) * hp)

private theorem u3x127Yf_mul (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    u3x127Yf z * u3x127Yfi z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![30 + -5 * z, 11 + 10 * z, -11 + 2 * z; 11 + 10 * z, -50 + -14 * z, 30 + -11 * z;
      -11 + 2 * z, 30 + -11 * z, 60 + 9 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![30 + 5 * z, 11 + -10 * z, -11 + -2 * z; 11 + -10 * z, -50 + 14 * z, 30 + 11 * z;
        -11 + -2 * z, 30 + 11 * z, 60 + -9 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-129) * hz + (10) * hp)
    (by linear_combination (212) * hz + (-6 + -6 * z) * hp)
    (by linear_combination (102) * hz + (-6 + 5 * z) * hp)
    (by linear_combination (212) * hz + (-6 + 6 * z) * hp)
    (by linear_combination (-417) * hz + (31) * hp)
    (by linear_combination (-75) * hz + (2 + -16 * z) * hp)
    (by linear_combination (102) * hz + (-6 + -5 * z) * hp)
    (by linear_combination (-75) * hz + (2 + 16 * z) * hp)
    (by linear_combination (-206) * hz + (38) * hp)

private theorem u3x127Yfi_mul (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    u3x127Yfi z * u3x127Yf z = 1 := by
  rw [Matrix.one_fin_three]
  show (!![30 + 5 * z, 11 + -10 * z, -11 + -2 * z; 11 + -10 * z, -50 + 14 * z, 30 + 11 * z;
      -11 + -2 * z, 30 + 11 * z, 60 + -9 * z] : Matrix (Fin 3) (Fin 3) K) *
    !![30 + -5 * z, 11 + 10 * z, -11 + 2 * z; 11 + 10 * z, -50 + -14 * z, 30 + -11 * z;
        -11 + 2 * z, 30 + -11 * z, 60 + 9 * z] = !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-129) * hz + (10) * hp)
    (by linear_combination (212) * hz + (-6 + 6 * z) * hp)
    (by linear_combination (102) * hz + (-6 + -5 * z) * hp)
    (by linear_combination (212) * hz + (-6 + -6 * z) * hp)
    (by linear_combination (-417) * hz + (31) * hp)
    (by linear_combination (-75) * hz + (2 + 16 * z) * hp)
    (by linear_combination (102) * hz + (-6 + 5 * z) * hp)
    (by linear_combination (-75) * hz + (2 + -16 * z) * hp)
    (by linear_combination (-206) * hz + (38) * hp)

private theorem det_u3x127X₁ (hp : (127 : K) = 0) (hz : z ^ 2 = -1) : (u3x127X₁ z).det = 1 := by
  rw [show u3x127X₁ z = !![6 + 15 * z, -49 + -16 * z, 7 + 35 * z;
      43 + -10 * z, -7 + 48 * z, 4 + 1 * z; 25 + -50 * z, 7 + 28 * z, -19] from rfl, det3_of]
  linear_combination (-7063 + 74580 * z) * hz + (-267 + -490 * z) * hp

private theorem det_u3x127X₂ (hp : (127 : K) = 0) (hz : z ^ 2 = -1) : (u3x127X₂ z).det = 1 := by
  rw [show u3x127X₂ z = !![23 + 31 * z, -1 + -28 * z, 54 + -12 * z; -1 + -20 * z, -2 + -56 * z, 4;
      14 + 33 * z, -5 + 49 * z, -37 + 1 * z] from rfl, det3_of]
  linear_combination (109842 + -12712 * z) * hz + (-834 + 843 * z) * hp

private theorem det_u3x127Yf (hp : (127 : K) = 0) (hz : z ^ 2 = -1) : (u3x127Yf z).det = 1 := by
  rw [show u3x127Yf z = !![30 + -5 * z, 11 + 10 * z, -11 + 2 * z;
      11 + 10 * z, -50 + -14 * z, 30 + -11 * z; -11 + 2 * z, 30 + -11 * z, 60 + 9 *
          z] from rfl, det3_of]
  linear_combination (-9520 + -49 * z) * hz + (-913 + -132 * z) * hp

private theorem map_u3x127X₁ (σ : K →+* K) (hσ : σ z = -z) :
    (u3x127X₁ z).map σ = (u3x127X₁i z)ᵀ := by
  rw [show u3x127X₁ z = !![6 + 15 * z, -49 + -16 * z, 7 + 35 * z;
      43 + -10 * z, -7 + 48 * z, 4 + 1 * z; 25 + -50 * z, 7 + 28 *
          z, -19] from rfl, map_fin_three_of]
  rw [show (u3x127X₁i z)ᵀ = !![6 + -15 * z, -49 + 16 * z, 7 + -35 * z;
      43 + 10 * z, -7 + -48 * z, 4 + -1 * z; 25 + 50 * z, 7 + -28 * z, -19] by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl]
  exact mat3_congr
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_neg, map_one, map_zero, map_ofNat])

private theorem map_u3x127X₂ (σ : K →+* K) (hσ : σ z = -z) :
    (u3x127X₂ z).map σ = (u3x127X₂i z)ᵀ := by
  rw [show u3x127X₂ z = !![23 + 31 * z, -1 + -28 * z, 54 + -12 * z; -1 + -20 * z, -2 + -56 * z, 4;
      14 + 33 * z, -5 + 49 * z, -37 + 1 * z] from rfl, map_fin_three_of]
  rw [show (u3x127X₂i z)ᵀ = !![23 + -31 * z, -1 + 28 * z, 54 + 12 * z; -1 + 20 * z, -2 + 56 * z, 4;
      14 + -33 * z, -5 + -49 * z, -37 + -1 * z] by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl]
  exact mat3_congr
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_neg, map_one, map_zero, map_ofNat])
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)

private theorem map_u3x127Yf (σ : K →+* K) (hσ : σ z = -z) :
    (u3x127Yf z).map σ = (u3x127Yfi z)ᵀ := by
  rw [show u3x127Yf z = !![30 + -5 * z, 11 + 10 * z, -11 + 2 * z;
      11 + 10 * z, -50 + -14 * z, 30 + -11 * z; -11 + 2 * z, 30 + -11 * z, 60 + 9 *
          z] from rfl, map_fin_three_of]
  rw [show (u3x127Yfi z)ᵀ = !![30 + 5 * z, 11 + -10 * z, -11 + -2 * z;
      11 + -10 * z, -50 + 14 * z, 30 + 11 * z; -11 + -2 * z, 30 + 11 * z, 60 + -9 * z] by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl]
  exact mat3_congr
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)
    (by simp only [map_add, map_mul, map_neg, map_one, map_zero, map_ofNat, hσ]; ring)

private theorem transpose_u3x127Yf : (u3x127Yf z)ᵀ = u3x127Yf z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem u3x127_w2 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![6 + 15 * z, -49 + -16 * z, 7 + 35 * z;
         43 + -10 * z, -7 + 48 * z, 4 + 1 * z;
         25 + -50 * z, 7 + 28 * z, -19] =
      !![-6 + -15 * z, 49 + 16 * z, -7 + -35 * z;
         -43 + 10 * z, 7 + -48 * z, -4 + -1 * z;
         25 + -50 * z, 7 + 28 * z, -19] := by
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

private theorem u3x127_w3 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-6 + -15 * z, 49 + 16 * z, -7 + -35 * z;
        -43 + 10 * z, 7 + -48 * z, -4 + -1 * z;
        25 + -50 * z, 7 + 28 * z, -19] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      !![6 + 15 * z, -49 + -16 * z, -7 + -35 * z;
         43 + -10 * z, -7 + 48 * z, -4 + -1 * z;
         -25 + 50 * z, -7 + -28 * z, -19] := by
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

private theorem u3x127_w4 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![6 + 15 * z, -49 + -16 * z, -7 + -35 * z;
        43 + -10 * z, -7 + 48 * z, -4 + -1 * z;
        -25 + 50 * z, -7 + -28 * z, -19] : Matrix (Fin 3) (Fin 3) K) *
      !![6 + -15 * z, 43 + 10 * z, 25 + 50 * z;
         -49 + 16 * z, -7 + -48 * z, 7 + -28 * z;
         7 + -35 * z, 4 + -1 * z, -19] =
      !![-7, 1 + -12 * z, 12 + 60 * z;
         1 + 12 * z, -33, 25 + 38 * z;
         -12 + 60 * z, -25 + 38 * z, -41] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (744) * hz + (13) * hp)
    (by linear_combination (953) * hz + (-3 + 24 * z) * hp)
    (by linear_combination (1198) * hz + (-10 + 20 * z) * hp)
    (by linear_combination (953) * hz + (-3 + -24 * z) * hp)
    (by linear_combination (-2403) * hz + (34) * hp)
    (by linear_combination (-1844) * hz + (23 + 19 * z) * hp)
    (by linear_combination (-1198) * hz + (10 + 20 * z) * hp)
    (by linear_combination (1844) * hz + (-23 + 19 * z) * hp)
    (by linear_combination (3284) * hz + (-28) * hp)

private theorem u3x127_w5 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-7, 1 + -12 * z, 12 + 60 * z;
        1 + 12 * z, -33, 25 + 38 * z;
        -12 + 60 * z, -25 + 38 * z, -41] : Matrix (Fin 3) (Fin 3) K) *
      !![23 + 31 * z, -1 + -28 * z, 54 + -12 * z;
         -1 + -20 * z, -2 + -56 * z, 4;
         14 + 33 * z, -5 + 49 * z, -37 + 1 * z] =
      !![-55 + -5 * z, 16 + -56 * z, 11 + -13 * z;
         50 + 38 * z, -62 + 49 * z, -8 + 17 * z;
         -20 + -10 * z, 11 + -28 * z, -35 + -61 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (2220) * hz + (-17 + 8 * z) * hp)
    (by linear_combination (3612) * hz + (-29 + 4 * z) * hp)
    (by linear_combination (60) * hz + (-7 + -17 * z) * hp)
    (by linear_combination (1626) * hz + (-10 + 18 * z) * hp)
    (by linear_combination (1526) * hz + (-12 + 22 * z) * hp)
    (by linear_combination (-106) * hz + (-7 + -6 * z) * hp)
    (by linear_combination (1100) * hz + (-15 + 1 * z) * hp)
    (by linear_combination (-3808) * hz + (32 + -3 * z) * hp)
    (by linear_combination (-720) * hz + (12 + 28 * z) * hp)

private theorem u3x127_w6 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-55 + -5 * z, 16 + -56 * z, 11 + -13 * z;
        50 + 38 * z, -62 + 49 * z, -8 + 17 * z;
        -20 + -10 * z, 11 + -28 * z, -35 + -61 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      !![55 + 5 * z, -16 + 56 * z, 11 + -13 * z;
         -50 + -38 * z, 62 + -49 * z, -8 + 17 * z;
         20 + 10 * z, -11 + 28 * z, -35 + -61 * z] := by
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

private theorem u3x127_w7 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![55 + 5 * z, -16 + 56 * z, 11 + -13 * z;
        -50 + -38 * z, 62 + -49 * z, -8 + 17 * z;
        20 + 10 * z, -11 + 28 * z, -35 + -61 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![23 + -31 * z, -1 + 20 * z, 14 + -33 * z;
         -1 + 28 * z, -2 + 56 * z, -5 + -49 * z;
         54 + 12 * z, 4, -37 + -1 * z] =
      !![-17 + 3 * z, -40 + 35 * z, 37 + -9 * z;
         -3 + -19 * z, -31 + 9 * z, -34 + -10 * z;
         -18 + 5 * z, -1 + -18 * z, -31 + 12 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (1257) * hz + (5 + -21 * z) * hp)
    (by linear_combination (3236) * hz + (-25) * hp)
    (by linear_combination (-2896) * hz + (26 + -6 * z) * hp)
    (by linear_combination (10) * hz + (-13 + 26 * z) * hp)
    (by linear_combination (-3504) * hz + (27 + 21 * z) * hp)
    (by linear_combination (3638) * hz + (-34 + -18 * z) * hp)
    (by linear_combination (-258) * hz + (-9 + -35 * z) * hp)
    (by linear_combination (1768) * hz + (-15 + -4 * z) * hp)
    (by linear_combination (-1641) * hz + (26 + 17 * z) * hp)

private theorem u3x127_word (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * u3x127X₁ z * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * u3x127X₁i z *
      u3x127X₂ z * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * u3x127X₂i z = u3x127Y z := by
  rw [show u3x127X₁ z = !![6 + 15 * z, -49 + -16 * z, 7 + 35 * z;
      43 + -10 * z, -7 + 48 * z, 4 + 1 * z; 25 + -50 * z, 7 + 28 * z, -19] from rfl,
    show u3x127X₁i z = !![6 + -15 * z, 43 + 10 * z, 25 + 50 * z;
        -49 + 16 * z, -7 + -48 * z, 7 + -28 * z; 7 + -35 * z, 4 + -1 * z, -19] from rfl,
    show u3x127X₂ z = !![23 + 31 * z, -1 + -28 * z, 54 + -12 * z; -1 + -20 * z, -2 + -56 * z, 4;
        14 + 33 * z, -5 + 49 * z, -37 + 1 * z] from rfl,
    show u3x127X₂i z = !![23 + -31 * z, -1 + 20 * z, 14 + -33 * z;
        -1 + 28 * z, -2 + 56 * z, -5 + -49 * z; 54 + 12 * z, 4, -37 + -1 * z] from rfl]
  rw [u3x127_w2 hp hz, u3x127_w3 hp hz, u3x127_w4 hp hz, u3x127_w5 hp hz, u3x127_w6 hp hz,
      u3x127_w7 hp hz]
  rfl

private theorem u3x127Y_sq2 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-17 + 3 * z, -40 + 35 * z, 37 + -9 * z;
        -3 + -19 * z, -31 + 9 * z, -34 + -10 * z;
        -18 + 5 * z, -1 + -18 * z, -31 + 12 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-17 + 3 * z, -40 + 35 * z, 37 + -9 * z;
         -3 + -19 * z, -31 + 9 * z, -34 + -10 * z;
         -18 + 5 * z, -1 + -18 * z, -31 + 12 * z] =
      !![63 + 11 * z, 31 + -23 * z, -58 + -57 * z;
         18 + -3 * z, -5 + -43 * z, 4 + -8 * z;
         -58 + -56 * z, -31 + 11 * z, 50 + -29 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-701) * hz + (3 + 7 * z) * hp)
    (by linear_combination (582) * hz + (10 + -22 * z) * hp)
    (by linear_combination (-485) * hz + (1 + 2 * z) * hp)
    (by linear_combination (-278) * hz + (8 + 7 * z) * hp)
    (by linear_combination (-404) * hz + (12 + 6 * z) * hp)
    (by linear_combination (-39) * hz + (16 + -6 * z) * hp)
    (by linear_combination (417) * hz + (4 + -3 * z) * hp)
    (by linear_combination (-203) * hz + (8 + 2 * z) * hp)
    (by linear_combination (279) * hz + (2 * z) * hp)

private theorem u3x127Y_sq4 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![63 + 11 * z, 31 + -23 * z, -58 + -57 * z;
        18 + -3 * z, -5 + -43 * z, 4 + -8 * z;
        -58 + -56 * z, -31 + 11 * z, 50 + -29 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![63 + 11 * z, 31 + -23 * z, -58 + -57 * z;
         18 + -3 * z, -5 + -43 * z, 4 + -8 * z;
         -58 + -56 * z, -31 + 11 * z, 50 + -29 * z] =
      !![-63 + -60 * z, 58 + -54 * z, -20 + -22 * z;
         14 + -2 * z, 26 + -39 * z, 40 + 24 * z;
         41 + -40 * z, -6 + 39 * z, 17 + 9 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (3382) * hz + (36 + 59 * z) * hp)
    (by linear_combination (109) * hz + (27 + -9 * z) * hp)
    (by linear_combination (1210) * hz + (-60 + -45 * z) * hp)
    (by linear_combination (544) * hz + (2 + -4 * z) * hp)
    (by linear_combination (1830) * hz + (-11 + 2 * z) * hp)
    (by linear_combination (747) * hz + (-13 + -12 * z) * hp)
    (by linear_combination (975) * hz + (-64 + -39 * z) * hp)
    (by linear_combination (496) * hz + (-29 + 18 * z) * hp)
    (by linear_combination (3945) * hz + (14 + 31 * z) * hp)

private theorem u3x127Y_sq8 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-63 + -60 * z, 58 + -54 * z, -20 + -22 * z;
        14 + -2 * z, 26 + -39 * z, 40 + 24 * z;
        41 + -40 * z, -6 + 39 * z, 17 + 9 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-63 + -60 * z, 58 + -54 * z, -20 + -22 * z;
         14 + -2 * z, 26 + -39 * z, 40 + 24 * z;
         41 + -40 * z, -6 + 39 * z, 17 + 9 * z] =
      !![8 + -18 * z, -37 + 53 * z, -15 + -6 * z;
         -21 + -23 * z, -47 + 40 * z, -43 + -55 * z;
         5 + 53 * z, -13 + -10 * z, -1 + -31 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (4588) * hz + (-5 + 52 * z) * hp)
    (by linear_combination (4488) * hz + (-51 + -35 * z) * hp)
    (by linear_combination (-174) * hz + (27 + 10 * z) * hp)
    (by linear_combination (-762) * hz + (15 + -15 * z) * hp)
    (by linear_combination (2565) * hz + (-10 + -12 * z) * hp)
    (by linear_combination (-676) * hz + (17 + -3 * z) * hp)
    (by linear_combination (1962) * hz + (-31 + 2 * z) * hp)
    (by linear_combination (990) * hz + (9 + -21 * z) * hp)
    (by linear_combination (1897) * hz + (-21 + 13 * z) * hp)

private theorem u3x127Y_sq16 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![8 + -18 * z, -37 + 53 * z, -15 + -6 * z;
        -21 + -23 * z, -47 + 40 * z, -43 + -55 * z;
        5 + 53 * z, -13 + -10 * z, -1 + -31 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![8 + -18 * z, -37 + 53 * z, -15 + -6 * z;
         -21 + -23 * z, -47 + 40 * z, -43 + -55 * z;
         5 + 53 * z, -13 + -10 * z, -1 + -31 * z] =
      !![-53 + 22 * z, 31 + 14 * z, 43 + -59 * z;
         -39 + 40 * z, -53 + 44 * z, -58 + 57 * z;
         8, 6 + -63 * z, 54 + 1 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-1213) * hz + (16 + -11 * z) * hp)
    (by linear_combination (1226) * hz + (3 + -21 * z) * hp)
    (by linear_combination (-2621) * hz + (32 + 4 * z) * hp)
    (by linear_combination (-3421) * hz + (32 + -17 * z) * hp)
    (by linear_combination (931) * hz + (21 + -23 * z) * hp)
    (by linear_combination (-357) * hz + (22 + 21 * z) * hp)
    (by linear_combination (-2367) * hz + (21 + 5 * z) * hp)
    (by linear_combination (2719) * hz + (-18 + -10 * z) * hp)
    (by linear_combination (1193) * hz + (-6 + 3 * z) * hp)

private theorem u3x127Y_sq32 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-53 + 22 * z, 31 + 14 * z, 43 + -59 * z;
        -39 + 40 * z, -53 + 44 * z, -58 + 57 * z;
        8, 6 + -63 * z, 54 + 1 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-53 + 22 * z, 31 + 14 * z, 43 + -59 * z;
         -39 + 40 * z, -53 + 44 * z, -58 + 57 * z;
         8, 6 + -63 * z, 54 + 1 * z] =
      !![11 + 49 * z, -49 + 39 * z, -53 + -20 * z;
         14 + -8 * z, 61 + 26 * z, -35 + -56 * z;
         8 + -40 * z, 41 + -62 * z, 25 + -51 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (1044) * hz + (7 + -17 * z) * hp)
    (by linear_combination (4641) * hz + (-60 + -20 * z) * hp)
    (by linear_combination (-559) * hz + (-9 + 15 * z) * hp)
    (by linear_combination (2640) * hz + (8 + -50 * z) * hp)
    (by linear_combination (-1095) * hz + (18) * hp)
    (by linear_combination (205) * hz + (-15 + 12 * z) * hp)
    (by linear_combination (-2520) * hz + (18 + 23 * z) * hp)
    (by linear_combination (-2835) * hz + (24 + 3 * z) * hp)
    (by linear_combination (-3590) * hz + (51 + 29 * z) * hp)

private theorem u3x127Y_sq64 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![11 + 49 * z, -49 + 39 * z, -53 + -20 * z;
        14 + -8 * z, 61 + 26 * z, -35 + -56 * z;
        8 + -40 * z, 41 + -62 * z, 25 + -51 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![11 + 49 * z, -49 + 39 * z, -53 + -20 * z;
         14 + -8 * z, 61 + 26 * z, -35 + -56 * z;
         8 + -40 * z, 41 + -62 * z, 25 + -51 * z] =
      !![59 + 39 * z, 40 + -52 * z, 46 + 3 * z;
         -23 + 29 * z, 50 + 47 * z, 22 + 13 * z;
         32 + 15 * z, -31 + -21 * z, 21 + 46 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (2889) * hz + (-31 + 31 * z) * hp)
    (by linear_combination (4165) * hz + (-78 + 13 * z) * hp)
    (by linear_combination (-2144) * hz + (15 + 6 * z) * hp)
    (by linear_combination (1640) * hz + (-7 + 11 * z) * hp)
    (by linear_combination (3836) * hz + (-18 + 31 * z) * hp)
    (by linear_combination (1560) * hz + (-42 + -30 * z) * hp)
    (by linear_combination (576) * hz + (2 + -21 * z) * hp)
    (by linear_combination (-10) * hz + (25 + -32 * z) * hp)
    (by linear_combination (6873) * hz + (-64 + -6 * z) * hp)

private theorem u3x127Y_sq128 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![59 + 39 * z, 40 + -52 * z, 46 + 3 * z;
        -23 + 29 * z, 50 + 47 * z, 22 + 13 * z;
        32 + 15 * z, -31 + -21 * z, 21 + 46 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![59 + 39 * z, 40 + -52 * z, 46 + 3 * z;
         -23 + 29 * z, 50 + 47 * z, 22 + 13 * z;
         32 + 15 * z, -31 + -21 * z, 21 + 46 * z] =
      !![38 + -3 * z, -24 + 15 * z, 28 + -30 * z;
         -47 + 24 * z, -38 + -32 * z, -30 + 43 * z;
         -60 + -52 * z, 34 + 23 * z, -22 + -52 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (58) * hz + (31 + 61 * z) * hp)
    (by linear_combination (-4535) * hz + (59 + -26 * z) * hp)
    (by linear_combination (-421) * hz + (39 + 28 * z) * hp)
    (by linear_combination (2689) * hz + (-35 + 15 * z) * hp)
    (by linear_combination (428) * hz + (4 + 49 * z) * hp)
    (by linear_combination (1296) * hz + (-6 + 33 * z) * hp)
    (by linear_combination (666) * hz + (21 + 28 * z) * hp)
    (by linear_combination (-2733) * hz + (14 + -43 * z) * hp)
    (by linear_combination (1888) * hz + (-5 + 15 * z) * hp)

private theorem u3x127Y_sq256 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![38 + -3 * z, -24 + 15 * z, 28 + -30 * z;
        -47 + 24 * z, -38 + -32 * z, -30 + 43 * z;
        -60 + -52 * z, 34 + 23 * z, -22 + -52 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![38 + -3 * z, -24 + 15 * z, 28 + -30 * z;
         -47 + 24 * z, -38 + -32 * z, -30 + 43 * z;
         -60 + -52 * z, 34 + 23 * z, -22 + -52 * z] =
      !![-21 + -22 * z, 8 + -44 * z, 16 + 54 * z;
         50 + -10 * z, -59 + 18 * z, -10 + -10 * z;
         -1 + 44 * z, -47 + 49 * z, 24 + -25 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (1929) * hz + (-8 + -9 * z) * hp)
    (by linear_combination (-1215) * hz + (17 + 4 * z) * hp)
    (by linear_combination (2295) * hz + (-9 + -28 * z) * hp)
    (by linear_combination (-3076) * hz + (38 + 5 * z) * hp)
    (by linear_combination (2373) * hz + (-6 + 15 * z) * hp)
    (by linear_combination (-4332) * hz + (38 + 16 * z) * hp)
    (by linear_combination (3412) * hz + (-47 + 17 * z) * hp)
    (by linear_combination (-2712) * hz + (17 + -31 * z) * hp)
    (by linear_combination (5253) * hz + (-59 + 27 * z) * hp)

private theorem u3x127Y_sq512 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-21 + -22 * z, 8 + -44 * z, 16 + 54 * z;
        50 + -10 * z, -59 + 18 * z, -10 + -10 * z;
        -1 + 44 * z, -47 + 49 * z, 24 + -25 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-21 + -22 * z, 8 + -44 * z, 16 + 54 * z;
         50 + -10 * z, -59 + 18 * z, -10 + -10 * z;
         -1 + 44 * z, -47 + 49 * z, 24 + -25 * z] =
      !![-62 + 56 * z, -23 + -44 * z, 34 + 24 * z;
         -34 + 43 * z, 13 + 21 * z, -31 + 39 * z;
         -49 + 51 * z, -21 + 26 * z, 43 + -62 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (3300) * hz + (-19 + -6 * z) * hp)
    (by linear_combination (2822) * hz + (-33 + 14 * z) * hp)
    (by linear_combination (-2098) * hz + (16 + -2 * z) * hp)
    (by linear_combination (-400) * hz + (-28 + 1 * z) * hp)
    (by linear_combination (274) * hz + (32 + -35 * z) * hp)
    (by linear_combination (-470) * hz + (13 + 23 * z) * hp)
    (by linear_combination (-2558) * hz + (2 + 24 * z) * hp)
    (by linear_combination (-2279) * hz + (31 + -8 * z) * hp)
    (by linear_combination (2511) * hz + (-12 + -4 * z) * hp)

private theorem u3x127Y_sq1024 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-62 + 56 * z, -23 + -44 * z, 34 + 24 * z;
        -34 + 43 * z, 13 + 21 * z, -31 + 39 * z;
        -49 + 51 * z, -21 + 26 * z, 43 + -62 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-62 + 56 * z, -23 + -44 * z, 34 + 24 * z;
         -34 + 43 * z, 13 + 21 * z, -31 + 39 * z;
         -49 + 51 * z, -21 + 26 * z, 43 + -62 * z] =
      !![-16 + -37 * z, 2 + 3 * z, 22 + 61 * z;
         44 + 38 * z, 7 + 63 * z, -39 + 37 * z;
         -56 + -49 * z, -41 + -2 * z, -41 + -49 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (2468) * hz + (4 + -46 * z) * hp)
    (by linear_combination (-2764) * hz + (25 + 6 * z) * hp)
    (by linear_combination (-1860) * hz + (15 + -2 * z) * hp)
    (by linear_combination (5300) * hz + (-17 + -65 * z) * hp)
    (by linear_combination (-437) * hz + (16 + -5 * z) * hp)
    (by linear_combination (-567) * hz + (-18 + 32 * z) * hp)
    (by linear_combination (812) * hz + (7 + -19 * z) * hp)
    (by linear_combination (-3310) * hz + (26 + 26 * z) * hp)
    (by linear_combination (6082) * hz + (-41 + -50 * z) * hp)

private theorem u3x127Y_q1 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-16 + -37 * z, 2 + 3 * z, 22 + 61 * z;
        44 + 38 * z, 7 + 63 * z, -39 + 37 * z;
        -56 + -49 * z, -41 + -2 * z, -41 + -49 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![38 + -3 * z, -24 + 15 * z, 28 + -30 * z;
         -47 + 24 * z, -38 + -32 * z, -30 + 43 * z;
         -60 + -52 * z, 34 + 23 * z, -22 + -52 * z] =
      !![-49 + -32 * z, 50 + 2 * z, 52 + 2 * z;
         18 + -22 * z, -21 + 31 * z, -51 + 4 * z;
         -7 + -52 * z, 4 + 4 * z, 61 + 37 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-2989) * hz + (8 + -49 * z) * hp)
    (by linear_combination (752) * hz + (2 + 24 * z) * hp)
    (by linear_combination (-1933) * hz + (7 + -24 * z) * hp)
    (by linear_combination (-526) * hz + (33 + -13 * z) * hp)
    (by linear_combination (-595) * hz + (-16 + -20 * z) * hp)
    (by linear_combination (-355) * hz + (18 + -5 * z) * hp)
    (by linear_combination (2647) * hz + (-3 + 20 * z) * hp)
    (by linear_combination (-1798) * hz + (26 + -7 * z) * hp)
    (by linear_combination (3932) * hz + (-27 + 14 * z) * hp)

private theorem u3x127Y_q2 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-49 + -32 * z, 50 + 2 * z, 52 + 2 * z;
        18 + -22 * z, -21 + 31 * z, -51 + 4 * z;
        -7 + -52 * z, 4 + 4 * z, 61 + 37 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![59 + 39 * z, 40 + -52 * z, 46 + 3 * z;
         -23 + 29 * z, 50 + 47 * z, 22 + 13 * z;
         32 + 15 * z, -31 + -21 * z, 21 + 46 * z] =
      !![53 + -27 * z, 6 + 24 * z, 43 + -15 * z;
         -61 + -15 * z, 4 + -52 * z, 44 + -17 * z;
         10 + 52 * z, -22 + 54 * z, -43 + 40 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-1160) * hz + (-10 + -12 * z) * hp)
    (by linear_combination (1716) * hz + (-22 + 20 * z) * hp)
    (by linear_combination (22) * hz + (-1 + 12 * z) * hp)
    (by linear_combination (101) * hz + (-1 + -20 * z) * hp)
    (by linear_combination (2517) * hz + (-10 + -2 * z) * hp)
    (by linear_combination (521) * hz + (-10 + -22 * z) * hp)
    (by linear_combination (-1357) * hz + (22 + -10 * z) * hp)
    (by linear_combination (2115) * hz + (-32 + -30 * z) * hp)
    (by linear_combination (1598) * hz + (-4 + 10 * z) * hp)

private theorem u3x127Y_q3 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![53 + -27 * z, 6 + 24 * z, 43 + -15 * z;
        -61 + -15 * z, 4 + -52 * z, 44 + -17 * z;
        10 + 52 * z, -22 + 54 * z, -43 + 40 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![8 + -18 * z, -37 + 53 * z, -15 + -6 * z;
         -21 + -23 * z, -47 + 40 * z, -43 + -55 * z;
         5 + 53 * z, -13 + -10 * z, -1 + -31 * z] =
      !![-23 + 11 * z, 59 + 18 * z, -22 + -53 * z;
         -28 + 34 * z, 11 + -39 * z, 16 + -10 * z;
         4 + -58 * z, 9 + 51 * z, 27 + -24 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-861) * hz + (11 + 3 * z) * hp)
    (by linear_combination (-321) * hz + (-20 + 21 * z) * hp)
    (by linear_combination (-693) * hz + (-3 + -20 * z) * hp)
    (by linear_combination (565) * hz + (-7 + 33 * z) * hp)
    (by linear_combination (-2705) * hz + (33 + -2 * z) * hp)
    (by linear_combination (3477) * hz + (-22 + 10 * z) * hp)
    (by linear_combination (-58) * hz + (3 + -19 * z) * hp)
    (by linear_combination (4516) * hz + (-26 + -39 * z) * hp)
    (by linear_combination (-4522) * hz + (42 + -5 * z) * hp)

private theorem u3x127Y_q4 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-23 + 11 * z, 59 + 18 * z, -22 + -53 * z;
        -28 + 34 * z, 11 + -39 * z, 16 + -10 * z;
        4 + -58 * z, 9 + 51 * z, 27 + -24 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-63 + -60 * z, 58 + -54 * z, -20 + -22 * z;
         14 + -2 * z, 26 + -39 * z, 40 + 24 * z;
         41 + -40 * z, -6 + 39 * z, 17 + 9 * z] =
      !![-51 + 36 * z, 12 + 15 * z, -61 + 53 * z;
         -55 + -48 * z, 33 + 58 * z, -2 + 11 * z;
         -55 + 14 * z, -30 + -11 * z, -21 + -12 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (1424) * hz + (-4 * z) * hp)
    (by linear_combination (-3363) * hz + (29 + -4 * z) * hp)
    (by linear_combination (-287) * hz + (22 + 10 * z) * hp)
    (by linear_combination (-1562) * hz + (33 + -16 * z) * hp)
    (by linear_combination (-705) * hz + (-6 + 21 * z) * hp)
    (by linear_combination (-1774) * hz + (24 + -11 * z) * hp)
    (by linear_combination (4338) * hz + (-26 + 16 * z) * hp)
    (by linear_combination (207) * hz + (1 + -11 * z) * hp)
    (by linear_combination (2284) * hz + (-12 + 25 * z) * hp)

private theorem u3x127Y_q5 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-51 + 36 * z, 12 + 15 * z, -61 + 53 * z;
        -55 + -48 * z, 33 + 58 * z, -2 + 11 * z;
        -55 + 14 * z, -30 + -11 * z, -21 + -12 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![63 + 11 * z, 31 + -23 * z, -58 + -57 * z;
         18 + -3 * z, -5 + -43 * z, 4 + -8 * z;
         -58 + -56 * z, -31 + 11 * z, 50 + -29 * z] =
      !![-17 + -3 * z, -3 + 19 * z, -18 + -5 * z;
         -40 + -35 * z, -31 + -9 * z, -1 + 18 * z;
         37 + 9 * z, -34 + 10 * z, -31 + -12 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-2617) * hz + (25 + 18 * z) * hp)
    (by linear_combination (-890) * hz + (9 + -5 * z) * hp)
    (by linear_combination (-3709) * hz + (29 + 41 * z) * hp)
    (by linear_combination (-1318) * hz + (-11 + -25 * z) * hp)
    (by linear_combination (-1269) * hz + (-4 + -18 * z) * hp)
    (by linear_combination (1953) * hz + (10 + 51 * z) * hp)
    (by linear_combination (859) * hz + (-29 + 16 * z) * hp)
    (by linear_combination (19) * hz + (-7 + 25 * z) * hp)
    (by linear_combination (-362) * hz + (19 + 20 * z) * hp)

private theorem u3x127Y_q6 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-17 + -3 * z, -3 + 19 * z, -18 + -5 * z;
        -40 + -35 * z, -31 + -9 * z, -1 + 18 * z;
        37 + 9 * z, -34 + 10 * z, -31 + -12 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-17 + 3 * z, -40 + 35 * z, 37 + -9 * z;
         -3 + -19 * z, -31 + 9 * z, -34 + -10 * z;
         -18 + 5 * z, -1 + -18 * z, -31 + 12 * z] =
      !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-395) * hz + (8) * hp)
    (by linear_combination (156) * hz + (5 + -6 * z) * hp)
    (by linear_combination (-223) * hz + (2 + -5 * z) * hp)
    (by linear_combination (156) * hz + (5 + 6 * z) * hp)
    (by linear_combination (-1630) * hz + (33) * hp)
    (by linear_combination (621) * hz + (-8 + -7 * z) * hp)
    (by linear_combination (-223) * hz + (2 + 5 * z) * hp)
    (by linear_combination (621) * hz + (-8 + 7 * z) * hp)
    (by linear_combination (-325) * hz + (30) * hp)

private theorem u3x127Y_pow (hp : (127 : K) = 0) (hz : z ^ 2 = -1) : u3x127Y z ^ 1231 = 1 := by
  show (!![-17 + 3 * z, -40 + 35 * z, 37 + -9 * z; -3 + -19 * z, -31 + 9 * z, -34 + -10 * z;
      -18 + 5 * z, -1 + -18 * z, -31 + 12 * z] : Matrix (Fin 3) (Fin 3) K) ^ 1231 = 1
  refine pow_eq_one_of_sq_chain_1231_127
    (u3x127Y_sq2 hp hz)
    (u3x127Y_sq4 hp hz)
    (u3x127Y_sq8 hp hz)
    (u3x127Y_sq16 hp hz)
    (u3x127Y_sq32 hp hz)
    (u3x127Y_sq64 hp hz)
    (u3x127Y_sq128 hp hz)
    (u3x127Y_sq256 hp hz)
    (u3x127Y_sq512 hp hz)
    (u3x127Y_sq1024 hp hz) ?_
  rw [u3x127Y_q1 hp hz, u3x127Y_q2 hp hz, u3x127Y_q3 hp hz, u3x127Y_q4 hp hz, u3x127Y_q5 hp hz,
      u3x127Y_q6 hp hz]
  exact Matrix.one_fin_three.symm

private theorem u3x127Yf_sq2 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![30 + -5 * z, 11 + 10 * z, -11 + 2 * z;
        11 + 10 * z, -50 + -14 * z, 30 + -11 * z;
        -11 + 2 * z, 30 + -11 * z, 60 + 9 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![30 + -5 * z, 11 + 10 * z, -11 + 2 * z;
         11 + 10 * z, -50 + -14 * z, 30 + -11 * z;
         -11 + 2 * z, 30 + -11 * z, 60 + 9 * z] =
      !![-3 + 3 * z, 43 + 26 * z, -50 + 61 * z;
         43 + 26 * z, 56 + -56 * z, -23 + 33 * z;
         -50 + 61 * z, -23 + 33 * z, -30 + -5 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (129) * hz + (8 + -1 * z) * hp)
    (by linear_combination (-212) * hz + (-3 + -2 * z) * hp)
    (by linear_combination (-102) * hz + (-4 + 2 * z) * hp)
    (by linear_combination (-212) * hz + (-3 + -2 * z) * hp)
    (by linear_combination (417) * hz + (24 + 8 * z) * hp)
    (by linear_combination (75) * hz + (1 + -3 * z) * hp)
    (by linear_combination (-102) * hz + (-4 + 2 * z) * hp)
    (by linear_combination (75) * hz + (1 + -3 * z) * hp)
    (by linear_combination (206) * hz + (35 + 3 * z) * hp)

private theorem u3x127Yf_sq4 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-3 + 3 * z, 43 + 26 * z, -50 + 61 * z;
        43 + 26 * z, 56 + -56 * z, -23 + 33 * z;
        -50 + 61 * z, -23 + 33 * z, -30 + -5 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-3 + 3 * z, 43 + 26 * z, -50 + 61 * z;
         43 + 26 * z, 56 + -56 * z, -23 + 33 * z;
         -50 + 61 * z, -23 + 33 * z, -30 + -5 * z] =
      !![-48 + 55 * z, -17 * z, 52 + 51 * z;
         -17 * z, -22 + 34 * z, -35 + 28 * z;
         52 + 51 * z, -35 + 28 * z, -17 + 48 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (4406) * hz + (-31 * z) * hp)
    (by linear_combination (635) * hz + (22 + -31 * z) * hp)
    (by linear_combination (736) * hz + (-1 + -9 * z) * hp)
    (by linear_combination (635) * hz + (22 + -31 * z) * hp)
    (by linear_combination (4901) * hz + (5 + -44 * z) * hp)
    (by linear_combination (-427) * hz + (-18 + 28 * z) * hp)
    (by linear_combination (736) * hz + (-1 + -9 * z) * hp)
    (by linear_combination (-427) * hz + (-18 + 28 * z) * hp)
    (by linear_combination (4835) * hz + (-7 + -58 * z) * hp)

private theorem u3x127Yf_sq8 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-48 + 55 * z, -17 * z, 52 + 51 * z;
        -17 * z, -22 + 34 * z, -35 + 28 * z;
        52 + 51 * z, -35 + 28 * z, -17 + 48 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-48 + 55 * z, -17 * z, 52 + 51 * z;
         -17 * z, -22 + 34 * z, -35 + 28 * z;
         52 + 51 * z, -35 + 28 * z, -17 + 48 * z] =
      !![-18 + 24 * z, 43 + -28 * z, -29 + -31 * z;
         43 + -28 * z, -12 + -27 * z, 63 + -20 * z;
         -29 + -31 * z, 63 + -20 * z, 53 + 61 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (5915) * hz + (-7) * hp)
    (by linear_combination (-85) * hz + (-14 + 7 * z) * hp)
    (by linear_combination (4777) * hz + (-64 + 21 * z) * hp)
    (by linear_combination (-85) * hz + (-14 + 7 * z) * hp)
    (by linear_combination (2229) * hz + (-4 + -27 * z) * hp)
    (by linear_combination (1429) * hz + (-1 + -38 * z) * hp)
    (by linear_combination (4777) * hz + (-64 + 21 * z) * hp)
    (by linear_combination (1429) * hz + (-1 + -38 * z) * hp)
    (by linear_combination (5689) * hz + (-12 + 13 * z) * hp)

private theorem u3x127Yf_q1 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![-18 + 24 * z, 43 + -28 * z, -29 + -31 * z;
        43 + -28 * z, -12 + -27 * z, 63 + -20 * z;
        -29 + -31 * z, 63 + -20 * z, 53 + 61 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![-48 + 55 * z, -17 * z, 52 + 51 * z;
         -17 * z, -22 + 34 * z, -35 + 28 * z;
         52 + 51 * z, -35 + 28 * z, -17 + 48 * z] =
      !![30 + 5 * z, 11 + -10 * z, -11 + -2 * z;
         11 + -10 * z, -50 + 14 * z, 30 + 11 * z;
         -11 + -2 * z, 30 + 11 * z, 60 + -9 * z] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (215) * hz + (-7 + -47 * z) * hp)
    (by linear_combination (-2228) * hz + (18 + 21 * z) * hp)
    (by linear_combination (-1048) * hz + (-7 + 13 * z) * hp)
    (by linear_combination (-2101) * hz + (26 + 48 * z) * hp)
    (by linear_combination (-1002) * hz + (-7 + 15 * z) * hp)
    (by linear_combination (-3144) * hz + (37 + 37 * z) * hp)
    (by linear_combination (1746) * hz + (19 + 37 * z) * hp)
    (by linear_combination (1555) * hz + (-38 + 19 * z) * hp)
    (by linear_combination (787) * hz + (-43 + 7 * z) * hp)

private theorem u3x127Yf_q2 (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    (!![30 + 5 * z, 11 + -10 * z, -11 + -2 * z;
        11 + -10 * z, -50 + 14 * z, 30 + 11 * z;
        -11 + -2 * z, 30 + 11 * z, 60 + -9 * z] : Matrix (Fin 3) (Fin 3) K) *
      !![30 + -5 * z, 11 + 10 * z, -11 + 2 * z;
         11 + 10 * z, -50 + -14 * z, 30 + -11 * z;
         -11 + 2 * z, 30 + -11 * z, 60 + 9 * z] =
      !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  rw [Matrix.mul_fin_three]
  exact mat3_congr
    (by linear_combination (-129) * hz + (10) * hp)
    (by linear_combination (212) * hz + (-6 + 6 * z) * hp)
    (by linear_combination (102) * hz + (-6 + -5 * z) * hp)
    (by linear_combination (212) * hz + (-6 + -6 * z) * hp)
    (by linear_combination (-417) * hz + (31) * hp)
    (by linear_combination (-75) * hz + (2 + 16 * z) * hp)
    (by linear_combination (102) * hz + (-6 + 5 * z) * hp)
    (by linear_combination (-75) * hz + (2 + -16 * z) * hp)
    (by linear_combination (-206) * hz + (38) * hp)

private theorem u3x127Yf_pow (hp : (127 : K) = 0) (hz : z ^ 2 = -1) : u3x127Yf z ^ 13 = 1 := by
  show (!![30 + -5 * z, 11 + 10 * z, -11 + 2 * z; 11 + 10 * z, -50 + -14 * z, 30 + -11 * z;
      -11 + 2 * z, 30 + -11 * z, 60 + 9 * z] : Matrix (Fin 3) (Fin 3) K) ^ 13 = 1
  refine pow_eq_one_of_sq_chain_13_127
    (u3x127Yf_sq2 hp hz)
    (u3x127Yf_sq4 hp hz)
    (u3x127Yf_sq8 hp hz) ?_
  rw [u3x127Yf_q1 hp hz, u3x127Yf_q2 hp hz]
  exact Matrix.one_fin_three.symm

private theorem u3x127Y_ne_one (hp : (127 : K) = 0) (hz : z ^ 2 = -1) : u3x127Y z ≠ 1 := by
  intro h1
  have e0 : u3x127Y z 0 1 = -40 + 35 * z := rfl
  have e : (-40 + 35 * z : K) = 0 := by
    rw [← e0, h1]
    simp
  exact one_ne_zero (α := K) (by
    linear_combination (41 * (-40 - 35 * z)) * e + (50225) * hz + (-912) * hp)

private theorem u3x127Yf_ne_one (hp : (127 : K) = 0) (hz : z ^ 2 = -1) : u3x127Yf z ≠ 1 := by
  intro h1
  have e0 : u3x127Yf z 0 1 = 11 + 10 * z := rfl
  have e : (11 + 10 * z : K) = 0 := by
    rw [← e0, h1]
    simp
  exact one_ne_zero (α := K) (by
    linear_combination (50 * (11 - 10 * z)) * e + (5000) * hz + (-87) * hp)

end Words

section Group

variable {K : Type} [Field K]

private theorem negNegOneDiag_eq_u3x127 :
    negNegOneDiag K = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negNegOneDiag]

private def u3x127X₁SU (h : UnitaryFieldData 127 1 K) {z : K}
    (hp : (127 : K) = 0) (hz : z ^ 2 = -1) (hbar : h.bar z = -z) : unitarySU 127 1 K 3 :=
  ⟨⟨u3x127X₁ z, u3x127X₁i z, u3x127X₁_mul hp hz, u3x127X₁i_mul hp hz⟩,
    (mem_unitarySU_iff h).mpr ⟨det_u3x127X₁ hp hz, by
      change ((u3x127X₁ z).map h.bar)ᵀ * u3x127X₁ z = 1
      rw [map_u3x127X₁ h.bar hbar, Matrix.transpose_transpose, u3x127X₁i_mul hp hz]⟩⟩

private def u3x127X₂SU (h : UnitaryFieldData 127 1 K) {z : K}
    (hp : (127 : K) = 0) (hz : z ^ 2 = -1) (hbar : h.bar z = -z) : unitarySU 127 1 K 3 :=
  ⟨⟨u3x127X₂ z, u3x127X₂i z, u3x127X₂_mul hp hz, u3x127X₂i_mul hp hz⟩,
    (mem_unitarySU_iff h).mpr ⟨det_u3x127X₂ hp hz, by
      change ((u3x127X₂ z).map h.bar)ᵀ * u3x127X₂ z = 1
      rw [map_u3x127X₂ h.bar hbar, Matrix.transpose_transpose, u3x127X₂i_mul hp hz]⟩⟩

private theorem excl1412_conj_U3_127 (h : UnitaryFieldData 127 1 K) {z : K}
    (hp : (127 : K) = 0) (hz : z ^ 2 = -1) (hbar : h.bar z = -z) :
    Excl1412 (MulAut.conj (unitaryProj h 3 (unitaryInvT h))) := by
  have : Fact (Nat.Prime 1231) := ⟨by norm_num⟩
  set x₁ := u3x127X₁SU h hp hz hbar with hx₁def
  set x₂ := u3x127X₂SU h hp hz hbar with hx₂def
  set τ := unitaryProj h 3 (unitaryInvT h) with hτdef
  have hτ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by
    rw [hτdef, ← map_mul, ← sq, unitaryInvT_sq, map_one])
  set y : unitarySU 127 1 K 3 :=
    unitaryInvT h * x₁ * unitaryInvT h * x₁⁻¹ * x₂ * unitaryInvT h * x₂⁻¹ with hydef
  have hy : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u3x127Y z := by
    rw [hydef, ← u3x127_word hp hz, ← negNegOneDiag_eq_u3x127, ← coe_unitaryInvT h]
    rfl
  have hyo : orderOf (unitaryProj h 3 y) = 1231 := by
    rw [orderOf_injective _ (unitaryProj_injective_exc h (by norm_num)) y, ← Subgroup.orderOf_coe,
      ← orderOf_units, hy]
    exact orderOf_eq_prime (u3x127Y_pow hp hz) (u3x127Y_ne_one hp hz)
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
  refine Or.inr (Or.inl ⟨unitaryProj h 3 x₁, unitaryProj h 3 x₂, a * b⁻¹ * a⁻¹ * b, 1231, 1,
    by norm_num, by norm_num, le_rfl, fun e he1 he12 => by
      interval_cases e <;> norm_num,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb))
      (Subgroup.inv_mem _ ha)) hb, ?_⟩)
  rw [pow_one, hw, Nat.Coprime.orderOf_pow (by rw [hyo]; norm_num), hyo]

private def u3x127YfGL {z : K} (hp : (127 : K) = 0) (hz : z ^ 2 = -1) : GL (Fin 3) K :=
  ⟨u3x127Yf z, u3x127Yfi z, u3x127Yf_mul hp hz, u3x127Yfi_mul hp hz⟩

private theorem u3x127YfGL_mem (h : UnitaryFieldData 127 1 K) {z : K}
    (hp : (127 : K) = 0) (hz : z ^ 2 = -1) (hbar : h.bar z =
        -z) : u3x127YfGL hp hz ∈ unitarySU 127 1 K 3 :=
  (mem_unitarySU_iff h).mpr ⟨det_u3x127Yf hp hz, by
    change ((u3x127Yf z).map h.bar)ᵀ * u3x127Yf z = 1
    rw [map_u3x127Yf h.bar hbar, Matrix.transpose_transpose, u3x127Yfi_mul hp hz]⟩

private theorem orderOf_u3x127YfGL {z : K} (hp : (127 : K) = 0) (hz : z ^ 2 = -1) :
    orderOf (u3x127YfGL hp hz) = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  rw [← orderOf_units]
  exact orderOf_eq_prime (u3x127Yf_pow hp hz) (u3x127Yf_ne_one hp hz)

end Group

theorem excl1412_U3_127 (K : Type) [Field K] (h : UnitaryFieldData 127 1 K)
    (α : MulAut (unitaryPSU h 3)) (hα : orderOf α = 2) : Excl1412 α := by
  obtain ⟨hp, z, hz, hbar⟩ := exists_sq_eq_neg_one_of_unitary_exc h (by norm_num)
  have hp' : (127 : K) = 0 := by exact_mod_cast hp
  exact excl1412_unitaryPSU3_of_exc h (by norm_num) (excl1412_conj_U3_127 h hp' hz hbar)
    (u3x127YfGL_mem h hp' hz hbar) transpose_u3x127Yf (q := 13) (k := 1) (by norm_num)
    (by norm_num) le_rfl (fun e he1 he8 => by interval_cases e <;> norm_num)
    (by rw [pow_one, orderOf_u3x127YfGL]) α hα

end CFSG.RankThree.PartTwo.Sec20

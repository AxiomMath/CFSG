module

public import Certificates.Certificate4192
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Syl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Inv

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15
open scoped MatrixGroups

theorem brute_two :
    ∀ a b c d e f g h i : ZMod 3, det3 a b c d e f g h i = 1 →
    (!![a, b, c; d, e, f; g, h, i] : M3) * !![a, b, c; d, e, f; g, h, i] = 1 →
    (!![a, b, c; d, e, f; g, h, i] : M3) ≠ 1 →
    (!![a, b, c; d, e, f; g, h, i] : M3) *
      (uM * !![a, b, c; d, e, f; g, h, i] * uM') =
      (uM * !![a, b, c; d, e, f; g, h, i] * uM') * !![a, b, c; d, e, f; g, h, i] →
    (!![a, b, c; d, e, f; g, h, i] : M3) *
      (lM * !![a, b, c; d, e, f; g, h, i] * lM') =
      (lM * !![a, b, c; d, e, f; g, h, i] * lM') * !![a, b, c; d, e, f; g, h, i] →
    (!![a, b, c; d, e, f; g, h, i] : M3) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] :=
  Certificates.certificate4192.1

theorem brute_thirteen :
    ∀ a b c d e f g h i : ZMod 3, det3 a b c d e f g h i = 1 →
    (!![a, b, c; d, e, f; g, h, i] : M3) *
      (uM * !![a, b, c; d, e, f; g, h, i] * uM') =
      (uM * !![a, b, c; d, e, f; g, h, i] * uM') * !![a, b, c; d, e, f; g, h, i] →
    (!![a, b, c; d, e, f; g, h, i] : M3) ^ 13 = 1 → (!![a, b, c; d, e, f; g, h, i] : M3) = 1 :=
  Certificates.certificate4192.2

theorem coe_upperUni_three : ((upperUni 3 : SL(3, ZMod 3)) : M3) = uM := rfl

theorem coe_lowerUni_three : ((lowerUni 3 : SL(3, ZMod 3)) : M3) = lM := rfl

theorem coe_upperUni_inv_three : (((upperUni 3)⁻¹ : SL(3, ZMod 3)) : M3) = uM' := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUni, uM', Matrix.adjugate_fin_three]

theorem coe_lowerUni_inv_three : (((lowerUni 3)⁻¹ : SL(3, ZMod 3)) : M3) = lM' := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUni, lM', Matrix.adjugate_fin_three]

theorem det3_of_mem (x : SL(3, ZMod 3)) :
    det3 ((x : M3) 0 0) ((x : M3) 0 1) ((x : M3) 0 2) ((x : M3) 1 0) ((x : M3) 1 1)
      ((x : M3) 1 2) ((x : M3) 2 0) ((x : M3) 2 1) ((x : M3) 2 2) = 1 := by
  have := x.2
  rw [Matrix.det_fin_three] at this
  exact this

theorem eq_zt_of_sq_eq_one {x : SL(3, ZMod 3)} (h2 : x * x = 1)
    (h1 : x ≠ 1)
    (hu : x * (upperUni 3 * x * (upperUni 3)⁻¹) = (upperUni 3 * x * (upperUni 3)⁻¹) * x)
    (hl : x * (lowerUni 3 * x * (lowerUni 3)⁻¹) = (lowerUni 3 * x * (lowerUni 3)⁻¹) * x) :
    x = zt 3 := by
  have hx := Matrix.eta_fin_three (x : M3)
  have h2' : (x : M3) * (x : M3) = 1 := by simpa using congrArg Subtype.val h2
  have h1' : (x : M3) ≠ 1 := fun h => h1 (Subtype.ext h)
  have hu' := congrArg Subtype.val hu
  have hl' := congrArg Subtype.val hl
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upperUni_three, coe_upperUni_inv_three,
    coe_lowerUni_three, coe_lowerUni_inv_three] at hu' hl'
  have key := brute_two _ _ _ _ _ _ _ _ _ (det3_of_mem x) (by rw [← hx]; exact h2')
    (by rw [← hx]; exact h1') (by rw [← hx]; exact hu') (by rw [← hx]; exact hl')
  apply Subtype.ext
  rw [coe_zt, ← key, ← hx]

theorem eq_one_of_pow_thirteen {x : SL(3, ZMod 3)}
    (h13 : x ^ 13 = 1)
    (hu : x * (upperUni 3 * x * (upperUni 3)⁻¹) = (upperUni 3 * x * (upperUni 3)⁻¹) * x) :
    x = 1 := by
  have hx := Matrix.eta_fin_three (x : M3)
  have h13' : (x : M3) ^ 13 = 1 := by simpa using congrArg Subtype.val h13
  have hu' := congrArg Subtype.val hu
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upperUni_three, coe_upperUni_inv_three] at hu'
  have key := brute_thirteen _ _ _ _ _ _ _ _ _ (det3_of_mem x) (by rw [← hx]; exact hu')
    (by rw [← hx]; exact h13')
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, ← key, ← hx]

end CFSG.Quasithin.E2P.Asc80

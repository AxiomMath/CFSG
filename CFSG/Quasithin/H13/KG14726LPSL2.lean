module

public import CFSG.Quasithin.H13.KG14726LSylow
public import CFSG.Quasithin.H13.KG14726COrd
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Assembly.LowTwoRank

theorem mul_self_eq_one_of_commute_sl2 {F : Type*} [Field F] [CharP F 2]
    {t y : Matrix.SpecialLinearGroup (Fin 2) F} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hy : y * t = t * y) : y * y = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdt : t 0 0 * t 1 1 - t 0 1 * t 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact t.2
  have hdy : y 0 0 * y 1 1 - y 0 1 * y 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact y.2
  have htt : (t : Matrix (Fin 2) (Fin 2) F) * t = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ht, Matrix.SpecialLinearGroup.coe_one]
  have hyt : (y : Matrix (Fin 2) (Fin 2) F) * t = t * y := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hy, Matrix.SpecialLinearGroup.coe_mul]
  have e00 : t 0 0 * t 0 0 + t 0 1 * t 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun htt 0) 0
  have e01 : t 0 0 * t 0 1 + t 0 1 * t 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun htt 0) 1
  have e10 : t 1 0 * t 0 0 + t 1 1 * t 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun htt 1) 0
  have e11 : t 1 0 * t 0 1 + t 1 1 * t 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun htt 1) 1
  have f01 : y 0 0 * t 0 1 + y 0 1 * t 1 1 = t 0 0 * y 0 1 + t 0 1 * y 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hyt 0) 1
  have f10 : y 1 0 * t 0 0 + y 1 1 * t 1 0 = t 1 0 * y 0 0 + t 1 1 * y 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hyt 1) 0
  have hsum : t 0 0 + t 1 1 = 0 := by
    by_contra hs
    have ha : t 0 0 = 0 := by
      have : (t 0 0 + t 1 1) * t 0 0 = 0 := by linear_combination e00 + hdt + h2
      exact (mul_eq_zero.mp this).resolve_left hs
    have hd : t 1 1 = 0 := by
      have : (t 0 0 + t 1 1) * t 1 1 = 0 := by linear_combination hdt + e11 + h2
      exact (mul_eq_zero.mp this).resolve_left hs
    have hb : t 0 1 = 0 := by
      have : (t 0 0 + t 1 1) * t 0 1 = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_left hs
    rw [ha, hd, hb] at hdt
    simp at hdt
  have hda : t 1 1 = t 0 0 := by linear_combination hsum - t 0 0 * h2
  have hps : y 0 0 = y 1 1 := by
    have hb : t 0 1 * (y 0 0 - y 1 1) = 0 := by linear_combination f01 - y 0 1 * hda
    have hc : t 1 0 * (y 1 1 - y 0 0) = 0 := by linear_combination f10 + y 1 0 * hda
    by_cases hb0 : t 0 1 = 0
    · by_cases hc0 : t 1 0 = 0
      · exfalso
        apply ht1
        have ha2 : (t 0 0 - 1) ^ 2 = 0 := by
          rw [hb0, hda] at hdt
          linear_combination hdt + (1 - t 0 0) * h2
        have ha : t 0 0 = 1 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha2
          linear_combination this
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha, hb0, hc0, hda]
      · have := (mul_eq_zero.mp hc).resolve_left hc0
        linear_combination -this
    · have := (mul_eq_zero.mp hb).resolve_left hb0
      linear_combination this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hdy + y 0 0 * hps + y 0 1 * y 1 0 * h2
  · linear_combination y 0 1 * y 0 0 * h2 - y 0 1 * hps
  · linear_combination y 1 0 * y 0 0 * h2 - y 1 0 * hps
  · linear_combination hdy - y 1 1 * hps + y 0 1 * y 1 0 * h2

theorem kg115L2Input_holds : KG115L2Input := by
  intro f X _ hf h
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 f h).2
  obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := h
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have hc : center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center, scalars_two_eq_bot]
  let e : X ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (eT.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  refine kg115Excluded_of_involution ?_ fun t y ht hy => ?_
  · rw [Nat.card_congr e.toEquiv, card_specialLinear_two, hK]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  · have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
    have htt : e t * e t = 1 := by rw [← map_mul, ← pow_two, ht2, map_one]
    have ht1 : e t ≠ 1 := by
      intro h1
      rw [MulEquiv.map_eq_one_iff] at h1
      rw [h1, orderOf_one] at ht
      exact absurd ht (by norm_num)
    have hyy := mul_self_eq_one_of_commute_sl2 (y := e y) htt ht1
      (by rw [← map_mul, ← map_mul, hy])
    rw [← map_mul, MulEquiv.map_eq_one_iff, ← pow_two] at hyy
    intro h3
    have := orderOf_dvd_of_pow_eq_one hyy
    rw [h3] at this
    exact absurd this (by norm_num)

end CFSG.Quasithin.H13.KG14726

end

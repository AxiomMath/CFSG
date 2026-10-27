module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFrame
public import CFSG.RankThree.Chevalley.SteinbergBTE6HighestRootGraph
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType.TwE6CorootCore

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction.TwistedE6Pilot CFSG.StandardType.TableBExcTwo
  CFSG.StandardType.TableBExcTwoFusion CFSG.RankThree.Chevalley

theorem exists_eq_nSL_of_conj_HSL {L : Type} [Field L] {l : Lˣ} (hl : l ^ 2 ≠ 1) {Q : SL2 L}
    (h : Q⁻¹ * HSL l * Q = HSL l⁻¹) : ∃ c : Lˣ, Q = nSL c := by
  have h' : HSL l * Q = Q * HSL l⁻¹ := by
    rw [← h]
    group
  have hll : (l : L) - ((l⁻¹ : Lˣ) : L) ≠ 0 := fun e => hl (by
    have e' : l = l⁻¹ := Units.ext (sub_eq_zero.1 e)
    rw [sq]
    nth_rewrite 2 [e']
    exact mul_inv_cancel l)
  have e := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L)) h'
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL] at e
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  have h00 : (Q : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := by
    refine (mul_eq_zero.1 (?_ : (Q : Matrix (Fin 2) (Fin 2) L) 0 0 *
      ((l : L) - ((l⁻¹ : Lˣ) : L)) = 0)).resolve_right hll
    simp only [Units.val_inv_eq_inv_val]
    linear_combination e00
  have h11 : (Q : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := by
    refine (mul_eq_zero.1 (?_ : (Q : Matrix (Fin 2) (Fin 2) L) 1 1 *
      ((l : L) - ((l⁻¹ : Lˣ) : L)) = 0)).resolve_right hll
    simp only [Units.val_inv_eq_inv_val]
    linear_combination -e11
  have hdet := det_SL2 Q
  rw [h00, h11, zero_mul, zero_sub] at hdet
  have h01 : (Q : Matrix (Fin 2) (Fin 2) L) 0 1 ≠ 0 := fun e => by
    rw [e, zero_mul, neg_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨Units.mk0 _ h01, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> simp [nSL, h00, h11]
  field_simp
  linear_combination -hdet

theorem exists_map_eq_mul_nSL_of_conj_HSL {L : Type} [Field L] {Fr : L →+* L} {P B : SL2 L}
    {l : Lˣ} (hl : l ^ 2 ≠ 1) (hP : P⁻¹ * B * P = HSL l)
    (hB : Matrix.SpecialLinearGroup.map Fr B = B)
    (hFl : Units.map Fr.toMonoidHom l = l⁻¹) :
    ∃ c : Lˣ, Matrix.SpecialLinearGroup.map Fr P = P * nSL c := by
  have hQ : (P⁻¹ * Matrix.SpecialLinearGroup.map Fr P)⁻¹ * HSL l *
      (P⁻¹ * Matrix.SpecialLinearGroup.map Fr P) = HSL l⁻¹ := by
    have e := congrArg (Matrix.SpecialLinearGroup.map Fr) hP
    rw [map_mul, map_mul, map_inv, hB, E6GraphLevi.map_HSL, hFl] at e
    rw [← e, ← hP]
    group
  obtain ⟨c, hc⟩ := exists_eq_nSL_of_conj_HSL hl hQ
  exact ⟨c, by rw [← hc]; group⟩

variable {L : Type} [Field L]

end CFSG.StandardType.TwE6CorootCore

end

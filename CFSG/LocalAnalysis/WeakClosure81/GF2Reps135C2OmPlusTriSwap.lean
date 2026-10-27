module

public import CFSG.Timmesfeld.RankTwo.SimplyLaced

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Timmesfeld
open scoped MatrixGroups

section BlockSwap

variable {F : Type} [Field F]

@[expose] noncomputable def sl3BlockSwapFun (A : SL(3, F)) : SL(3, F) :=
  ⟨(((A⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).transpose).submatrix
      ⇑Fin.revPerm ⇑Fin.revPerm, by
    rw [Matrix.det_submatrix_equiv_self Fin.revPerm, Matrix.det_transpose]
    exact (A⁻¹).2⟩

theorem coe_sl3BlockSwapFun (A : SL(3, F)) : (sl3BlockSwapFun A : Matrix (Fin 3) (Fin 3) F) =
    (((A⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).transpose).submatrix
      ⇑Fin.revPerm ⇑Fin.revPerm := rfl

@[expose] noncomputable def sl3BlockSwap : SL(3, F) →* SL(3, F) where
  toFun := sl3BlockSwapFun
  map_one' := by
    apply Subtype.ext
    rw [coe_sl3BlockSwapFun]
    simp
  map_mul' A B := by
    apply Subtype.ext
    rw [coe_sl3BlockSwapFun, Matrix.SpecialLinearGroup.coe_mul, coe_sl3BlockSwapFun,
      coe_sl3BlockSwapFun, Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, mul_inv_rev,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem tv_inv_eq_neg (i j : Fin 3) (h : i ≠ j) (c : F) : (tv i j c)⁻¹ = tv i j (-c) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  rw [tv_of_ne h c, tv_of_ne h (-c), Matrix.SpecialLinearGroup.coe_mul]
  simp only [Matrix.SpecialLinearGroup.transvection]
  rw [Matrix.transvection_mul_transvection_same i j h, add_neg_cancel, Matrix.transvection_zero]
  rfl

variable [CharP F 2]

theorem sl3BlockSwap_tv01 (c : F) : sl3BlockSwap (tv 0 1 c) = tv 1 2 c := by
  apply Subtype.ext
  change ((sl3BlockSwapFun (tv 0 1 c) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_sl3BlockSwapFun, tv_inv_eq_neg 0 1 (by decide) c,
    tv_of_ne (by decide : (0 : Fin 3) ≠ 1), tv_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single_apply,
      Matrix.one_apply, CharTwo.neg_eq]

theorem sl3BlockSwap_tv10 (c : F) : sl3BlockSwap (tv 1 0 c) = tv 2 1 c := by
  apply Subtype.ext
  change ((sl3BlockSwapFun (tv 1 0 c) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_sl3BlockSwapFun, tv_inv_eq_neg 1 0 (by decide) c,
    tv_of_ne (by decide : (1 : Fin 3) ≠ 0), tv_of_ne (by decide : (2 : Fin 3) ≠ 1)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single_apply,
      Matrix.one_apply, CharTwo.neg_eq]

theorem sl3BlockSwap_tv12 (c : F) : sl3BlockSwap (tv 1 2 c) = tv 0 1 c := by
  apply Subtype.ext
  change ((sl3BlockSwapFun (tv 1 2 c) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_sl3BlockSwapFun, tv_inv_eq_neg 1 2 (by decide) c,
    tv_of_ne (by decide : (1 : Fin 3) ≠ 2), tv_of_ne (by decide : (0 : Fin 3) ≠ 1)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single_apply,
      Matrix.one_apply, CharTwo.neg_eq]

theorem sl3BlockSwap_tv21 (c : F) : sl3BlockSwap (tv 2 1 c) = tv 1 0 c := by
  apply Subtype.ext
  change ((sl3BlockSwapFun (tv 2 1 c) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_sl3BlockSwapFun, tv_inv_eq_neg 2 1 (by decide) c,
    tv_of_ne (by decide : (2 : Fin 3) ≠ 1), tv_of_ne (by decide : (1 : Fin 3) ≠ 0)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single_apply,
      Matrix.one_apply, CharTwo.neg_eq]

theorem exists_sl3BlockSwap :
    ∃ θ : SL(3, F) →* SL(3, F), (∀ c : F, θ (tv 0 1 c) = tv 1 2 c) ∧
      (∀ c : F, θ (tv 1 0 c) = tv 2 1 c) ∧ (∀ c : F, θ (tv 1 2 c) = tv 0 1 c) ∧
      (∀ c : F, θ (tv 2 1 c) = tv 1 0 c) :=
  ⟨sl3BlockSwap, sl3BlockSwap_tv01, sl3BlockSwap_tv10, sl3BlockSwap_tv12, sl3BlockSwap_tv21⟩

end BlockSwap

end CFSG.LocalAnalysis.WeakClosure81

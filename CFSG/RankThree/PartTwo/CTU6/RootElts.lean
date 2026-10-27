module

public import CFSG.RankThree.PartTwo.CTU6.Embed
public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
public import CFSG.ClassicalInvolution.WeakCT.SpModel
public import CFSG.RankThree.PartOne.CTP.SpGeom
public import CFSG.RankThree.PartOne.CTP.Su4Std

public section

namespace CFSG.RankThree.PartTwo.CTU6

open Matrix CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.CTP
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open CFSG.ClassicalInvolution.WeakCT (blk blk_one_tv01 blk_one_tv10 hom_ext_sl2)
open CFSG.Timmesfeld (tv tv_of_ne)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem coe_tv {n : ℕ} {i j : Fin n} (h : i ≠ j) (c : F) :
    ((tv i j c : SL(n, F)) : Matrix (Fin n) (Fin n) F) = 1 + single i j c := by
  rw [tv_of_ne h, Matrix.SpecialLinearGroup.transvection_coe]

variable (σ : F ≃+* F)

theorem lowBlk_tv {i j : Fin 3} (h : i ≠ j) (c : F) :
    lowBlk σ (tv i j c) = 1 - single (Fin.rev j) (Fin.rev i) (σ c) := by
  have hinv : ((tv i j c)⁻¹ : SL(3, F)) = (1 + single i j (-c) : Matrix (Fin 3) (Fin 3) F) := by
    refine coe_inv_eq_of_mul_eq_one ?_
    have h0 : single i j (-c) * single i j c = (0 : Matrix (Fin 3) (Fin 3) F) := by
      simp [Ne.symm h]
    rw [coe_tv h, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, h0, add_zero,
      add_assoc, ← single_add, add_neg_cancel, single_zero, add_zero]
  rw [lowBlk, hinv, conjTr_add, conjTr_one, conjTr_single, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, antidiag_mul_self, antidiag_mul_single, single_mul_antidiag, map_neg,
    ← single_neg, ← sub_eq_add_neg]

variable (hσ : ∀ c, σ (σ c) = c)

theorem embSL3_tv01 (c : F) :
    embSL3 σ hσ (tv 0 1 c) =
      rootHom σ hσ (i := (0 : Fin 6)) (j := 1) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSL3, coe_rootHom, toAdd_ofAdd, embSL3Mat, lowBlk_tv σ (by decide), coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairMat_apply, rootMatrix, one_apply, Fin.rev]

theorem embSL3_tv10 (c : F) :
    embSL3 σ hσ (tv 1 0 c) =
      rootHom σ hσ (i := (1 : Fin 6)) (j := 0) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSL3, coe_rootHom, toAdd_ofAdd, embSL3Mat, lowBlk_tv σ (by decide), coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairMat_apply, rootMatrix, one_apply, Fin.rev]

theorem embSL3_tv12 (c : F) :
    embSL3 σ hσ (tv 1 2 c) =
      rootHom σ hσ (i := (1 : Fin 6)) (j := 2) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSL3, coe_rootHom, toAdd_ofAdd, embSL3Mat, lowBlk_tv σ (by decide), coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairMat_apply, rootMatrix, one_apply, Fin.rev]

theorem embSL3_tv21 (c : F) :
    embSL3 σ hσ (tv 2 1 c) =
      rootHom σ hσ (i := (2 : Fin 6)) (j := 1) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSL3, coe_rootHom, toAdd_ofAdd, embSL3Mat, lowBlk_tv σ (by decide), coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pairMat_apply, rootMatrix, one_apply, Fin.rev]

theorem embSU4_sbEmb_tv01 (c : F) :
    embSU4 σ (sbEmb σ hσ (tv 0 1 c)) =
      rootHom σ hσ (i := (1 : Fin 6)) (j := 2) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSU4, coe_rootHom, toAdd_ofAdd]
  change blockMat 6 1 (sbMat σ ((tv 0 1 c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) = _
  rw [coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, sbMat, rootMatrix, one_apply, Fin.rev]

theorem embSU4_sbEmb_tv10 (c : F) :
    embSU4 σ (sbEmb σ hσ (tv 1 0 c)) =
      rootHom σ hσ (i := (2 : Fin 6)) (j := 1) (by decide) (by decide) (by decide)
        (Multiplicative.ofAdd c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_embSU4, coe_rootHom, toAdd_ofAdd]
  change blockMat 6 1 (sbMat σ ((tv 1 0 c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) = _
  rw [coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, sbMat, rootMatrix, one_apply, Fin.rev]

theorem embSU4_comp_sbEmb : (embSU4 σ).comp (sbEmb σ hσ) = (embSL3 σ hσ).comp (blk F 1) := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, blk_one_tv01, embSU4_sbEmb_tv01,
      embSL3_tv12]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, blk_one_tv10, embSU4_sbEmb_tv10,
      embSL3_tv21]

end CFSG.RankThree.PartTwo.CTU6

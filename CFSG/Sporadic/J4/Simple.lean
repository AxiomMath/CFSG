module

public import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.J4.Criterion
import Certificates.Data.CFSGNative.J4.F2
import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4

open Native Matrix CFSG.Sporadic.Th

theorem eq_one_of_val {x : J}
    (h : ((x : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = 1) : x = 1 :=
  Subtype.ext (Units.ext h)

@[expose] noncomputable def cJ : J := ⟨conjGL, conjGL_mem⟩

section Facts

variable (hF : J4NativeFacts)
include hF

theorem ab_pow : ((a : J) * b) ^ 37 = 1 := by
  apply eq_one_of_val
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mul, Units.val_mul, a_coe,
    b_coe, gA_val hF.mat, gB_val hF.mat]
  have := congrArg rowsMatrix (eqRows_iff.1 hF.mat.ab37)
  rwa [rowsMatrix_powRows, rowsMatrix_mulRows, rowsMatrix_rowsA, rowsMatrix_rowsB,
    rowsMatrix_idRows] at this

theorem cJ_val : (((cJ : J) : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) =
    rowsMatrix conjRows := (conjRows_spec hF.mat).symm

theorem cJ_inv_val :
    (((cJ⁻¹ : J) : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) =
      rowsMatrix (invRows conjRows) := by
  have hc : rowsMatrix conjRows * rowsMatrix (invRows conjRows) = 1 := by
    have := congrArg rowsMatrix (eqRows_iff.1 hF.mat.cinv)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  rw [InvMemClass.coe_inv, Matrix.coe_units_inv, cJ_val hF]
  exact Matrix.inv_eq_right_inv hc

theorem z_pow : ((a : J) * (cJ⁻¹ * (a * b) * cJ)) ^ 43 = 1 := by
  apply eq_one_of_val
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [cJ_inv_val hF, cJ_val hF, a_coe, b_coe, gA_val hF.mat, gB_val hF.mat]
  have := congrArg rowsMatrix (eqRows_iff.1 hF.mat.z43)
  rw [rowsMatrix_powRows, zRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows,
    rowsMatrix_mulRows, rowsMatrix_rowsA, rowsMatrix_rowsB, rowsMatrix_idRows] at this
  rw [← this]
  simp only [Matrix.mul_assoc]

theorem card_J_N : Nat.card J = 86775571046077562880 := by
  have := isPretransitive_J hF
  have h := Subgroup.card_mul_index (MulAction.stabilizer J (root0 hF))
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_fin,
    stabilizer_eq_Hj hF, card_Hj_N hF] at h
  rw [← h]
  rfl

theorem isSimpleGroup_J_N : IsSimpleGroup J := by
  have := isPreprimitive_J hF
  have := faithful_J hF
  refine isSimpleGroup_of_conj_product (Ω := Fin nPts) ?_ a b cJ closure_ab (root0 hF)
    (ab_pow hF) (z_pow hF) ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · rw [stabilizer_eq_Hj hF, card_Hj_N hF]
    norm_num
  · rw [stabilizer_eq_Hj hF, card_Hj_N hF]
    norm_num

end Facts

theorem card_J (hF : J4Facts) : Nat.card J = 86775571046077562880 := hF.cardJ

theorem isSimpleGroup_J (hF : J4Facts) : IsSimpleGroup J := hF.simple

end CFSG.Sporadic.J4

module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockEmbed
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeAut

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm

theorem slGraphAut_slUpper2Hom (m : ℕ) (w : SpecialLinearGroup (Fin (m + 1)) F2) :
    slGraphAut (m + 1 + 1 + 1) F2 (slUpper2Hom m w) =
      slUpper2Hom m (slGraphAut (m + 1) F2 w) := by
  simp only [slUpper2Hom, MonoidHom.comp_apply, slGraphAut_slUpperBlockHom]

private theorem one_add_one_f2 : (1 : F2) + 1 = 0 := by
  linear_combination gf2_two

private theorem transvection_self_mul {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) *
      SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← SpecialLinearGroup.transvection_add, one_add_one_f2]
  exact SpecialLinearGroup.transvection_coeff_zero hij

private theorem omegaBlock_eq_xy (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 := by
  rw [omegaBlock, ← slPerm_swap_castSucc_succ gf2_two k,
    slPerm_swap_eq_transvections gf2_two
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne,
    mul_assoc, transvection_self_mul, mul_one]

private theorem graphAut_transvection_coe {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    (slGraphAut N F2 (SpecialLinearGroup.transvection hab (1 : F2)) :
        Matrix (Fin N) (Fin N) F2) = 1 + Matrix.single b a 1 := by
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  rw [slGraphAut_matrix, Matrix.SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, hneg]

private theorem graphAut_transvection {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    slGraphAut N F2 (SpecialLinearGroup.transvection hab (1 : F2)) =
      SpecialLinearGroup.transvection hab.symm (1 : F2) := by
  exact Subtype.ext (by
    simp only [graphAut_transvection_coe hab, SpecialLinearGroup.transvection_coe])

theorem slGraphAut_omegaBlock (n : ℕ) (k : Fin n) :
    slGraphAut (n + 1) F2 (omegaBlock n k) = (omegaBlock n k)⁻¹ := by
  let h : k.castSucc ≠ k.succ := (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
  have hxy : omegaBlock n k =
      SpecialLinearGroup.transvection h 1 * SpecialLinearGroup.transvection h.symm 1 :=
    omegaBlock_eq_xy n k
  have hx : SpecialLinearGroup.transvection h (1 : F2) *
      SpecialLinearGroup.transvection h 1 = 1 := transvection_self_mul h
  have hy : SpecialLinearGroup.transvection h.symm (1 : F2) *
      SpecialLinearGroup.transvection h.symm 1 = 1 := transvection_self_mul h.symm
  have hγx : slGraphAut (n + 1) F2 (SpecialLinearGroup.transvection h 1) =
      SpecialLinearGroup.transvection h.symm 1 := graphAut_transvection h
  have hγy : slGraphAut (n + 1) F2 (SpecialLinearGroup.transvection h.symm 1) =
      SpecialLinearGroup.transvection h 1 := graphAut_transvection h.symm
  rw [hxy, map_mul, hγx, hγy, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right hy,
    inv_eq_of_mul_eq_one_right hx]

theorem slGraphAut_mem_halfTorusK {n : ℕ} {t : SpecialLinearGroup (Fin (n + 1)) F2}
    (ht : t ∈ halfTorusK n) : slGraphAut (n + 1) F2 t ∈ halfTorusK n := by
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨k, hk, rfl⟩ := ht
    rw [slGraphAut_omegaBlock]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨k, hk, rfl⟩)
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

end CFSG.StandardType.GGHalf

end

module

public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Class
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp antiSpEquiv minorAut minorMap
  glMat antiIdx glMat_minorAut glMat_antiSpEquiv_symm minorMap_apply minorIdx_zero minorIdx_one
  minorIdx_two minorIdx_three antiIdx_inl_zero antiIdx_inl_one antiIdx_inr_zero antiIdx_inr_one
  antiIdx_symm_zero antiIdx_symm_one antiIdx_symm_two antiIdx_symm_three)
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [CharP F 2] [Finite F]

variable (F) in
@[expose] def sp4Graph : MulAut (StatedSp 2 F) :=
  ((antiSpEquiv F).symm.trans (minorAut F)).trans (antiSpEquiv F)

theorem coe_sp4Graph (g : StatedSp 2 F) :
    (((sp4Graph F g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (minorMap ((((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).submatrix antiIdx.symm antiIdx.symm)).submatrix
        antiIdx antiIdx := by
  change (glMat (minorAut F ((antiSpEquiv F).symm g) : GL (Fin 4) F)).submatrix antiIdx antiIdx = _
  rw [glMat_minorAut, glMat_antiSpEquiv_symm]

theorem coe_sp4Graph_sp4T :
    (((sp4Graph F (sp4T F) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks 0 !![0, -1; -1, 0] !![0, 1; 1, 0] (-1) := by
  rw [coe_sp4Graph, coe_sp4T]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three,
      antiIdx_inl_zero, antiIdx_inl_one, antiIdx_inr_zero, antiIdx_inr_one, antiIdx_symm_zero,
      antiIdx_symm_one, antiIdx_symm_two, antiIdx_symm_three, planeBlock,
      CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeMat]

theorem sp4Graph_sp4T_sq_add_add_one :
    (((sp4Graph F (sp4T F) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ^ 2 +
      (((sp4Graph F (sp4T F) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + 1 = 0 := by
  rw [coe_sp4Graph_sp4T]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply]

theorem exists_conj_sp4Graph_sp4T :
    ∃ g : StatedSp 2 F, sp4Graph F (sp4T F) = g * sp4TT F * g⁻¹ :=
  exists_conj_eq_sp4TT (by rw [← map_pow, sp4T_pow_three, map_one])
    ((sp4Graph F).map_ne_one_iff.mpr (sp4T_ne_one F)) sp4Graph_sp4T_sq_add_add_one

theorem exists_mulAut_apply_sp4T_eq {x : StatedSp 2 F} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ φ : MulAut (StatedSp 2 F), φ (sp4T F) = x := by
  by_cases hN : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ^ 2 +
      ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + 1 = 0
  · obtain ⟨h, rfl⟩ := exists_conj_eq_sp4TT hx3 hx1 hN
    obtain ⟨g, hg⟩ := exists_conj_sp4Graph_sp4T (F := F)
    refine ⟨(sp4Graph F).trans (MulAut.conj (h * g⁻¹)), ?_⟩
    rw [MulEquiv.trans_apply, hg, MulAut.conj_apply]
    group
  · obtain ⟨g, rfl⟩ := exists_conj_eq_sp4T hx3 hx1 hN
    exact ⟨MulAut.conj g, rfl⟩

omit [Finite F] in
theorem center_statedSp_eq_bot : Subgroup.center (StatedSp 2 F) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by norm_num)]

theorem nonempty_perfectResidual_centralizer_mulEquiv_sl2_of_pow_three (hF : 4 ≤ Nat.card F)
    {M : Type*} [Group M] (ψ : StatedSp 2 F ≃* M) {y : M} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer {y}) ≃* SL(2, F)) := by
  have h3 : (3 : F) ≠ 0 := by
    have h31 : (3 : F) = 1 := by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination h2
    rw [h31]
    exact one_ne_zero
  obtain ⟨φ, hφ⟩ := exists_mulAut_apply_sp4T_eq (x := ψ.symm y)
    (by rw [← map_pow, hy3, map_one]) (ψ.symm.map_ne_one_iff.mpr hy1)
  have h := nonempty_perfectResidual_centralizer_mulEquiv_sl2 h3 hF (φ.trans ψ)
  rwa [MulEquiv.trans_apply, hφ, MulEquiv.apply_symm_apply] at h

end CFSG.RankThree.PartTwo.KFacts

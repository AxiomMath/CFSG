module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClassFour
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankTransfer

public section

namespace CFSG.StandardType

namespace D4Rank

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

section Inv

theorem omFixDim_of_gl_conj (B : GL (Fin (2 * 4)) K) {w y : Om8 K}
    (h : (w : GL (Fin (2 * 4)) K) = B * y * B⁻¹) : omFixDim w = omFixDim y := by
  have e : omRep w = (matrixLinearIso B).toLinearMap * omRep y *
      (matrixLinearIso B⁻¹).toLinearMap := by
    refine LinearMap.ext fun v => ?_
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe, matrixLinearIso_apply, omRep_apply]
    rw [h, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [omFixDim, omFixDim, e]
  refine fixDim_conj ?_ ?_
  · refine LinearMap.ext fun v => ?_
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe, matrixLinearIso_apply,
      Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec,
      Module.End.one_apply]
  · refine LinearMap.ext fun v => ?_
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe, matrixLinearIso_apply,
      Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Module.End.one_apply]

theorem omFixDim_plusRefl [Finite K] [CharP K 2] (y : Om8 K) :
    omFixDim (AutOm.plusRefl one_le_four y) = omFixDim y :=
  omFixDim_of_gl_conj _ (reflAut_apply_val _ _ y)

theorem free_of_omFixDim_zero {x : Om8 K} (h : omFixDim x = 0) :
    ∀ y, act x y = y → y = 0 := by
  intro y hy
  have hbot := Submodule.finrank_eq_zero.mp h
  have hmem : y ∈ LinearMap.ker (omRep x - 1) := mem_ker_iff_act.mpr hy
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

end Inv

section Main

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem Q_e2f2 : coordinateQuadPlus 4 K (AutOm.pvec 2 true + AutOm.pvec 2 false) = 1 := by
  have h := AutOm.polar_pvec_not (K := K) (n := 4) 2 true
  rw [polar, AutOm.form_pvec, AutOm.form_pvec, sub_zero, sub_zero] at h
  exact h

omit [Finite K] [CharP K 2] in
theorem mulAut_conj (α : MulAut (Om8 K)) (h y : Om8 K) :
    α (h * y * h⁻¹) = MulAut.conj (α h) (α y) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem exists_conj_x0 {x : Om8 K} (hx3 : x ^ 3 = 1) (hd : omFixDim x = 6) :
    ∃ h : Om8 K, x = h * x0 * h⁻¹ :=
  exists_conj_of_C1 hx3 x0_pow_three hd omFixDim_x0 Q_e2f2 x0_fix_e2f2

theorem exists_conj_plusRefl_x0 :
    ∃ h : Om8 K, AutOm.plusRefl one_le_four (x0 (K := K)) = h * x0 * h⁻¹ :=
  exists_conj_x0 (by rw [← map_pow, x0_pow_three, map_one])
    (by rw [omFixDim_plusRefl, omFixDim_x0])

theorem omFixDim_theta_inv_x0 : omFixDim ((theta : MulAut (Om8 K))⁻¹ (x0 (K := K))) = 0 := by
  obtain ⟨h, hh⟩ := exists_conj_plusRefl_x0 (K := K)
  rw [← plusRefl_theta_plusRefl, MulAut.mul_apply, MulAut.mul_apply, hh, omFixDim_plusRefl,
    mulAut_conj, omFixDim_conj, omFixDim_theta_x0]

theorem plusRefl_mul_theta :
    AutOm.plusRefl one_le_four * (theta : MulAut (Om8 K)) =
      theta⁻¹ * AutOm.plusRefl one_le_four := by
  rw [← plusRefl_theta_plusRefl, mul_assoc _ (AutOm.plusRefl one_le_four),
    AutOm.plusRefl_mul_self, mul_one]

theorem _root_.CFSG.StandardType.D4Rank.ggD4TrialityClassInput_holds :
    GGD4TrialityClassInput := by
  intro K _ _ _ x hx3
  refine ⟨fun hd6 => ?_, fun hd0 => ?_⟩
  · obtain ⟨h, rfl⟩ := exists_conj_x0 hx3 hd6
    refine ⟨?_, ?_⟩
    · rw [mulAut_conj, omFixDim_conj, omFixDim_theta_x0]
    · rw [mulAut_conj, omFixDim_conj, omFixDim_theta_inv_x0]
  · have hz3 : (theta (x0 (K := K))) ^ 3 = 1 := by rw [← map_pow, x0_pow_three, map_one]
    obtain ⟨h, hh | hh⟩ := exists_conj_of_C4 hx3 hz3 (free_of_omFixDim_zero hd0)
      (free_of_omFixDim_zero omFixDim_theta_x0)
    · refine Or.inr ?_
      rw [hh, mulAut_conj, omFixDim_conj, MulAut.inv_apply_self, omFixDim_x0]
    · refine Or.inl ?_
      obtain ⟨h', hh'⟩ := exists_conj_plusRefl_x0 (K := K)
      have e : AutOm.plusRefl one_le_four (theta (x0 (K := K))) =
          (theta : MulAut (Om8 K))⁻¹ (h' * x0 * h'⁻¹) := by
        rw [← MulAut.mul_apply, plusRefl_mul_theta, MulAut.mul_apply, hh']
      rw [hh, e, mulAut_conj (theta⁻¹), mulAut_conj, omFixDim_conj, MulAut.conj_apply,
        mulAut_conj, omFixDim_conj, MulAut.apply_inv_self, omFixDim_x0]

end Main

end D4Rank

theorem ggD4TrialityCentRankInput_holds :
    GGD4TrialityCentRankInput :=
  ggD4TrialityCentRankInput_of_classInput D4Rank.ggD4TrialityClassInput_holds

theorem ggHypSixD4SemilinearInput_of_bstarRank
    (hR : GGHypSixD4BstarRankInput) : GGHypSixD4SemilinearInput :=
  ggHypSixD4SemilinearInput_of_rank ggD4TrialityCentRankInput_holds hR


end CFSG.StandardType

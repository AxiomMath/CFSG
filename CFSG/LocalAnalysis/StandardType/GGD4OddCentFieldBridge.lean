module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark
public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeField
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.Bal207.D4Graph (isoAdj isoAdj_mk sigmaOmega val_sigmaOmega
  thetaOmega_sigmaOmega)
open CFSG.LieType.Universal.Spin (isPerfect_statedOmega_quadPlus)
open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge (thetaOmega thetaOmega_surjective)
open CFSG.ClassicalGroups.Orthogonal (isSimpleGroup_statedProj_statedOmega_quadPlus)

section Simple

theorem d4Recipe_isSimpleGroup (K : Type) [Field K] :
    IsSimpleGroup (D4Recipe K) ∧ ∃ x y : D4Recipe K, x * y ≠ y * x := by
  have hsimple : IsSimpleGroup (D4Recipe K) :=
    isSimpleGroup_statedProj_statedOmega_quadPlus (K := K) (n := 4) (by norm_num)
  refine ⟨hsimple, ?_⟩
  haveI hperfOmega : Group.IsPerfect (LargeEvenOmega (LargeEvenQPlus K 4)) :=
    isPerfect_statedOmega_quadPlus (K := K) (n := 4) (by norm_num)
  have hperf : Group.IsPerfect (D4Recipe K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hnc : ¬ IsMulCommutative (D4Recipe K) := hperf.not_isMulCommutative
  rw [isMulCommutative_iff] at hnc
  push Not at hnc
  exact hnc

end Simple

section Bridge


theorem d4Recipe_congr_isoAdj_of_mem_fieldSet {K : Type} [Field K] [Finite K]
    {f : MulAut (D4Recipe K)} (hf : f ∈ D4FieldSet K) :
    ∃ τ : K ≃+* K, MulAut.congr (isoAdj K) f = entrywiseAdjointAut Tag.D4 τ := by
  obtain ⟨σ, hσ⟩ := hf
  refine ⟨σ, MulEquiv.ext fun y => ?_⟩
  obtain ⟨A, rfl⟩ := thetaOmega_surjective K y
  have hsymm : (isoAdj K).symm (thetaOmega K A) = QuotientGroup.mk A := by
    rw [MulEquiv.symm_apply_eq]
    exact (isoAdj_mk K A).symm
  have hfA : f (QuotientGroup.mk A) = QuotientGroup.mk (sigmaOmega σ A) :=
    hσ A (sigmaOmega σ A) (val_sigmaOmega σ A)
  change isoAdj K (f ((isoAdj K).symm (thetaOmega K A))) =
    entrywiseAdjointAut Tag.D4 σ (thetaOmega K A)
  rw [hsymm, hfA, isoAdj_mk, thetaOmega_sigmaOmega]

end Bridge

end CFSG.StandardType

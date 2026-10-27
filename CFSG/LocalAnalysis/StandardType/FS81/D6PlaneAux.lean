module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Model
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusNode
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusCore
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightF6Eigen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapPair
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.SeitzReduction.OmegaPilot
open scoped MatrixGroups

@[expose] def d6PlaneQ (x : Fin 4 → ZMod 2) : ZMod 2 := x 0 * x 2 + x 1 * x 3

@[expose] def d6PlaneB (x y : Fin 4 → ZMod 2) : ZMod 2 :=
  x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1

@[expose] noncomputable def d6PlaneEmbMat : Matrix (Fin 6 ⊕ Fin 6) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j =>
    match i with
    | Sum.inl a =>
      if a = 2 then (if j = 0 then 1 else 0) else if a = 3 then (if j = 1 then 1 else 0) else 0
    | Sum.inr a =>
      if a = 2 then (if j = 2 then 1 else 0) else if a = 3 then (if j = 3 then 1 else 0) else 0

@[expose] noncomputable def d6PlaneEmb : (Fin 4 → ZMod 2) →ₗ[ZMod 2] V12 :=
  Matrix.toLin' d6PlaneEmbMat

theorem d6PlaneEmb_inl_two (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inl 2) = x 0 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inl_three (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inl 3) = x 1 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inr_two (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inr 2) = x 2 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inr_three (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inr 3) = x 3 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inl_zero (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inl 0) = 0 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inl_one (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inl 1) = 0 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inl_four (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inl 4) = 0 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inl_five (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inl 5) = 0 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inr_zero (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inr 0) = 0 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inr_one (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inr 1) = 0 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inr_four (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inr 4) = 0 := by
  revert x; decide +kernel

theorem d6PlaneEmb_inr_five (x : Fin 4 → ZMod 2) : d6PlaneEmb x (Sum.inr 5) = 0 := by
  revert x; decide +kernel

theorem d6PlaneEmb_injective : Function.Injective d6PlaneEmb := by
  intro x y h
  funext j
  fin_cases j
  · simpa [d6PlaneEmb_inl_two] using congrFun h (Sum.inl 2)
  · simpa [d6PlaneEmb_inl_three] using congrFun h (Sum.inl 3)
  · simpa [d6PlaneEmb_inr_two] using congrFun h (Sum.inr 2)
  · simpa [d6PlaneEmb_inr_three] using congrFun h (Sum.inr 3)

theorem d6PlaneQ_emb (x : Fin 4 → ZMod 2) : Q12 (d6PlaneEmb x) = d6PlaneQ x := by
  rw [show Q12 = CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2) from rfl,
    CFSG.LieType.Universal.Spin.quadPlus_apply]
  revert x; decide +kernel

theorem d6PlaneB_emb (x y : Fin 4 → ZMod 2) :
    QuadraticMap.polar Q12 (d6PlaneEmb x) (d6PlaneEmb y) = d6PlaneB x y := by
  rw [show Q12 = CFSG.LieType.Universal.Spin.quadPlus 6 (ZMod 2) from rfl,
    CFSG.LieType.Universal.Spin.polar_quadPlus]
  revert x y; decide +kernel

theorem d6PlaneEmb_inl_other (x : Fin 4 → ZMod 2) {i : Fin 6}
    (h : i ∉ ({2,3} : Finset (Fin 6))) :
    d6PlaneEmb x (Sum.inl i) = 0 ∧ d6PlaneEmb x (Sum.inr i) = 0 := by
  revert x
  fin_cases i <;> simp_all <;> decide +kernel

theorem d6mem_Y2_iff (v : V12) :
    v ∈ Y2 ↔ ∃ x : Fin 4 → ZMod 2, d6PlaneEmb x = v := by
  rw [Y2, mem_planeSpan]
  constructor
  · intro hv
    refine ⟨![v (Sum.inl 2), v (Sum.inl 3), v (Sum.inr 2), v (Sum.inr 3)], ?_⟩
    funext j
    rcases j with i | i <;> fin_cases i <;>
      simp [d6PlaneEmb_inl_zero, d6PlaneEmb_inl_one, d6PlaneEmb_inl_two, d6PlaneEmb_inl_three,
        d6PlaneEmb_inl_four, d6PlaneEmb_inl_five, d6PlaneEmb_inr_zero, d6PlaneEmb_inr_one,
        d6PlaneEmb_inr_two, d6PlaneEmb_inr_three, d6PlaneEmb_inr_four, d6PlaneEmb_inr_five,
        hv]
  · rintro ⟨x, rfl⟩ i hi
    exact d6PlaneEmb_inl_other x hi

theorem d6PlaneEmb_mem_Y2 (x : Fin 4 → ZMod 2) : d6PlaneEmb x ∈ Y2 :=
  (d6mem_Y2_iff _).mpr ⟨x, rfl⟩

abbrev d6PlaneSL : Type := Matrix.SpecialLinearGroup ↥({2,3} : Finset (Fin 6)) (ZMod 2)

@[expose] def d6PlaneE2 : ↥({2,3} : Finset (Fin 6)) := ⟨2, by decide⟩

@[expose] def d6PlaneE3 : ↥({2,3} : Finset (Fin 6)) := ⟨3, by decide⟩

@[expose] noncomputable def d6PlaneNmat (A : d6PlaneSL) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![A d6PlaneE2 d6PlaneE2, A d6PlaneE2 d6PlaneE3, 0, 0;
     A d6PlaneE3 d6PlaneE2, A d6PlaneE3 d6PlaneE3, 0, 0;
     0, 0, (A⁻¹ : d6PlaneSL) d6PlaneE2 d6PlaneE2, (A⁻¹ : d6PlaneSL) d6PlaneE3 d6PlaneE2;
     0, 0, (A⁻¹ : d6PlaneSL) d6PlaneE2 d6PlaneE3, (A⁻¹ : d6PlaneSL) d6PlaneE3 d6PlaneE3]

@[expose] noncomputable def d6PlaneFmat (A : d6PlaneSL) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  (d6PlaneNmat A).submatrix (Equiv.swap 1 3) (Equiv.swap 1 3)

theorem d6PlaneNmat_mul_inv (A : d6PlaneSL) :
    d6PlaneNmat A * d6PlaneNmat A⁻¹ = 1 := by
  revert A; decide +kernel

theorem d6PlaneNmat_inv_mul (A : d6PlaneSL) :
    d6PlaneNmat A⁻¹ * d6PlaneNmat A = 1 := by
  revert A; decide +kernel

theorem d6PlaneFmat_mul_inv (A : d6PlaneSL) :
    d6PlaneFmat A * d6PlaneFmat A⁻¹ = 1 := by
  revert A; decide +kernel

theorem d6PlaneFmat_inv_mul (A : d6PlaneSL) :
    d6PlaneFmat A⁻¹ * d6PlaneFmat A = 1 := by
  revert A; decide +kernel

@[expose] noncomputable def d6PlaneNle (A : d6PlaneSL) :
    (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  LinearEquiv.ofLinear (Matrix.toLin' (d6PlaneNmat A)) (Matrix.toLin' (d6PlaneNmat A⁻¹))
    (by rw [← Matrix.toLin'_mul, d6PlaneNmat_mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, d6PlaneNmat_inv_mul, Matrix.toLin'_one])

@[expose] noncomputable def d6PlaneFle (A : d6PlaneSL) :
    (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  LinearEquiv.ofLinear (Matrix.toLin' (d6PlaneFmat A)) (Matrix.toLin' (d6PlaneFmat A⁻¹))
    (by rw [← Matrix.toLin'_mul, d6PlaneFmat_mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, d6PlaneFmat_inv_mul, Matrix.toLin'_one])

theorem d6PlaneNle_mul_inv (A : d6PlaneSL) : d6PlaneNle A * d6PlaneNle A⁻¹ = 1 := by
  refine LinearEquiv.ext fun x => ?_
  revert A x; decide +kernel

theorem d6PlaneFle_mul_inv (A : d6PlaneSL) : d6PlaneFle A * d6PlaneFle A⁻¹ = 1 := by
  refine LinearEquiv.ext fun x => ?_
  revert A x; decide +kernel

theorem d6PlaneNle_apply_inv (A : d6PlaneSL) (x : Fin 4 → ZMod 2) :
    d6PlaneNle A (d6PlaneNle A⁻¹ x) = x := by
  have h := congrArg (fun e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) => e x)
    (d6PlaneNle_mul_inv A)
  simpa [LinearEquiv.mul_apply] using h

theorem d6PlaneFle_apply_inv (A : d6PlaneSL) (x : Fin 4 → ZMod 2) :
    d6PlaneFle A (d6PlaneFle A⁻¹ x) = x := by
  have h := congrArg (fun e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) => e x)
    (d6PlaneFle_mul_inv A)
  simpa [LinearEquiv.mul_apply] using h

theorem d6PlaneNode_apply_emb (A : d6PlaneSL) (x : Fin 4 → ZMod 2) :
    lin (siegelParam (ZMod 2) {2,3} ∅ A) (d6PlaneEmb x) = d6PlaneEmb (d6PlaneNle A x) := by
  change lin (siegelParam (ZMod 2) {2,3} ∅ A) (d6PlaneEmb x) =
    d6PlaneEmb (Matrix.toLin' (d6PlaneNmat A) x)
  simp only [lin, MulEquiv.coe_toMonoidHom, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  rw [siegelParam_coe]
  revert A x
  decide +kernel

theorem d6PlaneFlip_apply_emb (A : d6PlaneSL) (x : Fin 4 → ZMod 2) :
    lin (siegelParam (ZMod 2) {2,3} {3} A) (d6PlaneEmb x) =
      d6PlaneEmb (d6PlaneFle A x) := by
  change lin (siegelParam (ZMod 2) {2,3} {3} A) (d6PlaneEmb x) =
    d6PlaneEmb (Matrix.toLin' (d6PlaneFmat A) x)
  simp only [lin, MulEquiv.coe_toMonoidHom, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  rw [siegelParam_coe]
  revert A x
  decide +kernel

theorem d6PlaneMap_apply_emb (A B : d6PlaneSL) (x : Fin 4 → ZMod 2) :
    (lin (siegelParam (ZMod 2) {2,3} ∅ B) * lin (siegelParam (ZMod 2) {2,3} {3} A))
        (d6PlaneEmb x) = d6PlaneEmb ((d6PlaneNle B * d6PlaneFle A) x) := by
  rw [LinearEquiv.mul_apply, d6PlaneFlip_apply_emb, d6PlaneNode_apply_emb,
    LinearEquiv.mul_apply]

theorem d6PlaneMap_inv_apply (A B : d6PlaneSL) (x : Fin 4 → ZMod 2) :
    (lin (siegelParam (ZMod 2) {2,3} ∅ B) * lin (siegelParam (ZMod 2) {2,3} {3} A))
        (d6PlaneEmb ((d6PlaneFle A⁻¹ * d6PlaneNle B⁻¹) x)) = d6PlaneEmb x := by
  rw [d6PlaneMap_apply_emb, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    d6PlaneFle_apply_inv, d6PlaneNle_apply_inv]

theorem d6PlaneNode_inv_apply (B : d6PlaneSL) (x : Fin 4 → ZMod 2) :
    ((lin (siegelParam (ZMod 2) {2,3} ∅ B) : (Fin 6 ⊕ Fin 6 → ZMod 2) ≃ₗ[ZMod 2] _))
        (d6PlaneEmb (d6PlaneNle B⁻¹ x)) = d6PlaneEmb x := by
  rw [d6PlaneNode_apply_emb, d6PlaneNle_apply_inv]

end CFSG.StandardType.FrameRoute.FS81.D6M

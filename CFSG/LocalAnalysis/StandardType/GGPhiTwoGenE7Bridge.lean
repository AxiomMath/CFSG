module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7Two
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenLabels
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.RouteD.MultiModelGlue
public import CFSG.ClassicalInvolution.RouteD.MultiStarStd
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.ClassicalInvolution.RouteD.TypeEModel
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LieType.SeitzGeneration.OrthNonsplitLow
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.LieType.SeitzGeneration.ExcHigh

theorem exists_mulEquiv_e7D6Group_rPlus
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) :
    ∃ _θ : ↥(e7D6Group K) ≃* OrthRest.RPlus K 6, commutator ↥(e7D6Group K) = ⊤ ∧
      ∀ z : ↥(e7D6Group K), (∀ x : ↥(e7D6Group K), z * x = x * z) → z = 1 := by
  classical
  have hZspin : Subgroup.center
      (spinGroup (CFSG.LieType.Universal.Spin.quadPlus 6 K)) = ⊥ :=
    (OrthRest.spinPlus_bij (K := K) (n := 6) (by norm_num)).2
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D6_E7 K
  have hinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : x ∈ Subgroup.center
        (spinGroup (CFSG.LieType.Universal.Spin.quadPlus 6 K)) := hker hx
    rwa [hZspin] at hx'
  let e1 : spinGroup (CFSG.LieType.Universal.Spin.quadPlus 6 K) ≃* ↥(e7D6Group K) :=
    (MulEquiv.ofBijective Ψ.rangeRestrict
        ⟨fun x y h => hinj (Subtype.ext_iff.mp h), MonoidHom.rangeRestrict_surjective Ψ⟩).trans
      (MulEquiv.subgroupCongr hrange)
  let eSpin : spinGroup (CFSG.LieType.Universal.Spin.quadPlus 6 K) ≃* OrthRest.RPlus K 6 :=
    MulEquiv.ofBijective _ (OrthRest.spinPlus_bij (K := K) (n := 6) (by norm_num)).1
  let θ : ↥(e7D6Group K) ≃* OrthRest.RPlus K 6 := e1.symm.trans eSpin
  have hcenter : Subgroup.center ↥(e7D6Group K) = ⊥ := by
    have hmap := Subgroup.map_center_eq e1
    rw [hZspin, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hperf : commutator ↥(e7D6Group K) = ⊤ := by
    have hperfS : Group.IsPerfect
        (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 6 K)) :=
      CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := K) (n := 6)
        (by norm_num)
    haveI : Group.IsPerfect (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 6 K)) := hperfS
    have hperfD : Group.IsPerfect ↥(e7D6Group K) :=
      Group.IsPerfect.ofSurjective
        (f := (θ.trans (rPlusEquivStatedOmega K 6)).symm.toMonoidHom)
        (θ.trans (rPlusEquivStatedOmega K 6)).symm.surjective
    exact hperfD.commutator_eq_top
  refine ⟨θ, hperf, ?_⟩
  intro z hz
  have hz' : z ∈ Subgroup.center ↥(e7D6Group K) :=
    Subgroup.mem_center_iff.mpr (fun g => (hz g).symm)
  rw [hcenter] at hz'
  exact Subgroup.mem_bot.mp hz'

end CFSG.StandardType.PhiTwoRootGen

end

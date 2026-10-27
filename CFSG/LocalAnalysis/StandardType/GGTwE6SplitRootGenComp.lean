module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenFix
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenRoot
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyNormalizer
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoAssembly
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.SeitzGeneration.ExcHigh.Product
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.TwE6SplitRootGen

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction.F4Pilot
  CFSG.HardMathSupport.Timmesfeld.Torality

private theorem rootChar_zetaVec_frameCoord_eq_one {K : Type} [Field K] {τ : Tag} {p : ℕ}
    [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (x : Fin τ.rank → ZMod p)
    (β : Fin τ.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ x) β = 1 ↔
      ∑ j, (β j : ZMod p) * x j = 0 := by
  rw [CFSG.StandardType.NoOffE8Five.rootChar_zetaVec]
  constructor
  · intro h
    have h1 : Multiplicative.ofAdd (∑ j, (β j : ZMod p) * x j) = 1 :=
      (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ) (by rw [h, map_one])
    simpa using congrArg Multiplicative.toAdd h1
  · intro h
    rw [h]
    simp

theorem familyKernel_frameCoord_twE6Split {K : Type}
    [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (a : Fin Tag.F4.rank) :
    familyKernel (fun s : {s : Fin Tag.F4.rank → ZMod p //
        TableBExc.torusAct .F4 p (simple Tag.F4 a) s = s} =>
      TableBExc.E6Three.zetaVec ζ hζ
        (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s.1))) =
      signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)) := by
  ext β
  simp only [familyKernel, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hβ, hβ1⟩
    refine (forall_fix_sum_frameCoord_iff hp2 hβ a).1 fun s hs => ?_
    exact (rootChar_zetaVec_frameCoord_eq_one hζo hζ
      (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s)) β).1
      (hβ1 ⟨s, hs⟩)
  · intro hβ
    have hβroot : IsRoot TwistTag.E6.tag β := isRoot_of_mem_signedSimpleRoots hβ
    refine ⟨hβroot, fun s => ?_⟩
    exact (rootChar_zetaVec_frameCoord_eq_one hζo hζ
      (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s.1)) β).2
      ((forall_fix_sum_frameCoord_iff hp2 hβroot a).2 hβ s.1 s.2)


variable {K : Type} [Field K]

theorem isComponentOf_orbitRankOneGroup_twE6Split [Finite K] [CharP K 2] (σ : K →+* K) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hζσ : σ (ζ : K) = ζ) (a : Fin Tag.F4.rank) :
    IsComponentOf ((orbitRankOneGroup TwistTag.E6 K σ a).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ))
      (Subgroup.centralizer (SuSplitRootGen.torusFix (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ)
        (TableBExc.torusAct .F4 p (simple Tag.F4 a)))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let C₀ := graphFixedRootGroup TwistTag.E6 K σ
  let T := ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ
  let f : (Fin Tag.F4.rank → ZMod p) → Fin Tag.F4.rank → ZMod p :=
    TableBExc.torusAct .F4 p (simple Tag.F4 a)
  let ι := {s : Fin Tag.F4.rank → ZMod p // f s = s}
  let b : ι → Fin TwistTag.E6.tag.rank → Kˣ := fun s =>
    TableBExc.E6Three.zetaVec ζ hζ
      (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s.1))
  let u : ι → ↥C₀ := fun s => T (Multiplicative.ofAdd s.1)
  have hu : ∀ s : ι, (u s : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (b s) := fun _ => rfl
  have hfix : SuSplitRootGen.torusFix T f = Set.range u := by
    ext y
    simp only [SuSplitRootGen.torusFix, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨Multiplicative.toAdd x, hx⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Multiplicative.ofAdd s.1, s.2, rfl⟩
  have hker : familyKernel b = signedSimpleRoots
      (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)) :=
    familyKernel_frameCoord_twE6Split hp2 hζo hζ a
  have hXmap : (Subgroup.centralizer (SuSplitRootGen.torusFix T f)).map C₀.subtype ≤
      familyCentralizer TwistTag.E6.tag K b := by
    rintro g ⟨x, hx, rfl⟩
    rw [mem_familyCentralizer]
    refine ⟨CFSG.SeitzReduction.TwistedE6Pilot.graphFixedRootGroup_le_adjointGroup' σ x.2,
      fun s => ?_⟩
    have hxs : u s ∈ SuSplitRootGen.torusFix T f := by
      rw [hfix]
      exact Set.mem_range_self s
    have hcomm := (Subgroup.mem_centralizer_iff.1 hx) (u s) hxs
    have hcoe := congrArg (fun z : ↥C₀ => (z : ModGL TwistTag.E6.tag K)) hcomm
    simp only [Subgroup.coe_mul] at hcoe
    rw [hu s] at hcoe
    change rootDiagUnit TwistTag.E6.tag (b s) * (x : ModGL TwistTag.E6.tag K) *
      (rootDiagUnit TwistTag.E6.tag (b s))⁻¹ = (x : ModGL TwistTag.E6.tag K)
    rw [hcoe, mul_assoc, mul_inv_cancel, mul_one]
  have hXnorm : (Subgroup.centralizer (SuSplitRootGen.torusFix T f)).map C₀.subtype ≤
      Subgroup.normalizer (rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank))) :
        Set (ModGL TwistTag.E6.tag K)) := by
    have h := hXmap.trans (familyCentralizer_le_normalizer_rootSpan b)
    rwa [hker] at h
  have hQinf : rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank))) ⊓ C₀ =
      orbitRankOneGroup TwistTag.E6 K σ a := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      exact rootSpan_inf_twistedFixedGroup_le_twE6 σ a
        ⟨hx.1, graphFixedRootGroup_le (t := TwistTag.E6) (K := K) (σ := σ) hx.2⟩
    · intro x hx
      exact Subgroup.mem_inf.2
        ⟨orbitRankOneGroup_le_rootSpan_twE6 σ a hx,
          CFSG.LieType.SeitzGeneration.ExcHigh.orbitRankOneGroup_le_graphFixedRootGroup' σ a hx⟩
  have hLX : (orbitRankOneGroup TwistTag.E6 K σ a).subgroupOf C₀ ≤
      Subgroup.centralizer (SuSplitRootGen.torusFix T f) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy
    rw [hfix] at hy
    obtain ⟨s, rfl⟩ := hy
    apply Subtype.ext
    have hxQ : (x : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank))) :=
      orbitRankOneGroup_le_rootSpan_twE6 σ a hx
    have hS : signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)) ⊆
        rootCharKernel (b s) := by
      intro β hβ
      refine ⟨isRoot_of_mem_signedSimpleRoots hβ, ?_⟩
      exact (rootChar_zetaVec_frameCoord_eq_one hζo hζ
        (ExcFrames.frameCoord TwistTag.E6.tag p (ExcFrames.twE6SplitTheta p s.1)) β).2
        ((forall_fix_sum_frameCoord_iff hp2 (isRoot_of_mem_signedSimpleRoots hβ) a).2 hβ
          s.1 s.2)
    have hcomm := (Subgroup.mem_centralizer_iff.1
      (rootSpan_le_centralizer (b s) hS hxQ))
      (rootDiagUnit TwistTag.E6.tag (b s)) (Set.mem_singleton _)
    simp only [Subgroup.coe_mul]
    rw [hu s]
    exact hcomm
  refine ⟨hLX, ?_, ?_⟩
  · refine CFSG.Assembly.IsSubnormal.step hLX ?_ (CFSG.Assembly.IsSubnormal.refl _)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLX]
    have hQL : (rootSpan TwistTag.E6.tag K
          (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)))).subgroupOf
          C₀ = (orbitRankOneGroup TwistTag.E6 K σ a).subgroupOf C₀ := by
      rw [← Subgroup.inf_subgroupOf_right
        (rootSpan TwistTag.E6.tag K
          (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)))) C₀,
        hQinf]
    rw [← hQL]
    rw [← Subgroup.inf_subgroupOf_right
      (rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank)))) C₀]
    rw [← Subgroup.subgroupOf_normalizer_eq
      (H := rootSpan TwistTag.E6.tag K
        (signedSimpleRoots (↑(TwistTag.E6.orbit a) : Set (Fin TwistTag.E6.tag.rank))) ⊓ C₀)
      (N := C₀) inf_le_right]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hXnorm (Subgroup.mem_map.2 ⟨x, hx, rfl⟩), Subgroup.le_normalizer x.2⟩
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe
        (CFSG.LieType.SeitzGeneration.ExcHigh.orbitRankOneGroup_le_graphFixedRootGroup' σ a))
      (isQuasisimple_orbitRankOneGroup_twE6 σ (Fact.out : p.Prime) hp2 hζo hζσ a)

theorem dvd_card_orbitRankOneGroup_subgroupOf_twE6Split [CharP K 2] (σ : K →+* K) {p : ℕ}
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζσ : σ (ζ : K) = ζ) (a : Fin Tag.F4.rank) :
    p ∣ Nat.card ↥((orbitRankOneGroup TwistTag.E6 K σ a).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (CFSG.LieType.SeitzGeneration.ExcHigh.orbitRankOneGroup_le_graphFixedRootGroup' σ a)).toEquiv]
  exact dvd_card_orbitRankOneGroup_twE6 σ hζo hζσ a

end CFSG.StandardType.TwE6SplitRootGen

end

module

public import CFSG.LocalAnalysis.StandardType.GGKGAdjDefs
public import CFSG.LocalAnalysis.StandardType.GGKGOrthPairs
public import CFSG.LocalAnalysis.StandardType.GGKGSigmaLayer
public import CFSG.LocalAnalysis.StandardType.GGKGMult
import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSLFourBasic
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYSplit
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.GH74.Statements
import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
import CFSG.LieType.Chevalley.C2E6StandardBetaStar
import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder
import CFSG.LieType.Chevalley.C2E6StandardLeviFactors
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2FiveSixKinds
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixInner
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallAltK
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallestAut
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatU6Sporadic
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B1MoreElevenD
import CFSG.Quasithin.Background.B1MoreElevenF
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.HN.CertificateBase
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyChain11
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Certificates.Certificate10
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate3
import Certificates.Certificate3085Base
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE
  CFSG.SeitzReduction CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem zetaVec_pow_three_eq_one {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) :
    zetaVec ζ hζ x ^ 3 = 1 := by
  funext i
  simp only [Pi.pow_apply, zetaVec_apply]
  rw [← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow]
  rfl

private theorem exists_mul_ne_mul_of_isPerfect (S : Type) [Group S] [Nontrivial S]
    [Group.IsPerfect S] : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  have hcm : ∀ a b : S, a * b = b * a := by
    intro a b
    by_contra hab
    exact h ⟨a, b, hab⟩
  exact Group.IsPerfect.not_isMulCommutative S (isMulCommutative_iff.mpr hcm)

private theorem mem_setD_iff {i : Fin 6} :
    i ∈ C2E6Std.setD ↔ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  simp [C2E6Std.setD]

private theorem notMem_setD_iff {i : Fin 6} : i ∉ C2E6Std.setD ↔ i = 0 ∨ i = 5 := by
  fin_cases i <;> simp [C2E6Std.setD]


theorem isQuasisimple_rootSpan_a3 {K : Type} [Field K] [Finite K]
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (hαβ : iform α β = 0) :
    IsQuasisimple (rootSpan Tag.E6 K {γ | IsRoot Tag.E6 γ ∧ iform γ α = 0 ∧ iform γ β = 0}) := by
  obtain ⟨v, hv⟩ := exists_weyl_sigmaSetE6A3_eq hα hβ hαβ
  rw [← hv, ← rhoSigmaE6A3_range (L := K) v]
  exact CFSG.SeitzReduction.SporadicRefine.isQuasisimple_of_mulEquiv_SL_four
    (MonoidHom.ofInjective (f := rhoSigmaE6A3 K v) (rhoSigmaE6A3_injective v)).symm

private theorem isQuasisimple_rootSpan_smul {K : Type} [Field K] (u : WeylGroup Tag.E6)
    {S : Set (Fin Tag.E6.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot Tag.E6 γ)
    (h : IsQuasisimple (rootSpan Tag.E6 K S)) :
    IsQuasisimple (rootSpan Tag.E6 K ((fun γ => u • γ) '' S)) := by
  rw [← map_conj_rootSpan (τ := Tag.E6) (L := K) u hS]
  exact (CFSG.IsQuasisimple.congr (Subgroup.equivMapOfInjective (rootSpan Tag.E6 K S)
    (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) K u)).toMonoidHom
    (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) K u)).injective)).mp h

private theorem isQuasisimple_rootSpan_setD {K : Type} [Field K] [Finite K] [CharP K 2] :
    IsQuasisimple (rootSpan Tag.E6 K {γ | IsRoot Tag.E6 γ ∧ γ 0 = 0 ∧ γ 5 = 0}) := by
  have hset : {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ γ 0 = 0 ∧ γ 5 = 0} =
      parabolicRoots Tag.E6 C2E6Std.setD := by
    ext γ
    constructor
    · rintro ⟨hγ, h0, h5⟩
      refine ⟨hγ, fun i hi => ?_⟩
      rcases notMem_setD_iff.mp hi with h | h
      · rw [h]; exact h0
      · rw [h]; exact h5
    · rintro ⟨hγ, h⟩
      exact ⟨hγ, h 0 (notMem_setD_iff.mpr (Or.inl rfl)),
        h 5 (notMem_setD_iff.mpr (Or.inr rfl))⟩
  rw [hset, ← subsystemGroup_eq_rootSpan (τ := Tag.E6) (K := K) (J := C2E6Std.setD)]
  change IsQuasisimple (TwistedE6Pilot.d4Levi K)
  haveI : IsSimpleGroup (TwistedE6Pilot.d4Levi K) := TwistedE6Pilot.isSimpleGroup_d4Levi (K := K)
  haveI : Group.IsPerfect (TwistedE6Pilot.d4Levi K) := TwistedE6Pilot.isPerfect_d4Levi (K := K)
  exact CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup
    (exists_mul_ne_mul_of_isPerfect (TwistedE6Pilot.d4Levi K))

theorem isQuasisimple_rootSpan_d4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (hαβ : iform α β = 0) :
    IsQuasisimple (rootSpan Tag.E6 K
      {γ | IsRoot Tag.E6 γ ∧ ((iform γ α + iform γ β : ℤ) : ZMod 3) = 0}) := by
  obtain ⟨u, hu⟩ := exists_weyl_smul_d4 hα hβ hαβ
  rw [← hu]
  exact isQuasisimple_rootSpan_smul u (fun γ h => h.1) isQuasisimple_rootSpan_setD

theorem kgAdjL2 : KGAdjL2 := by
  intro K _ _ hchar ζ hζ hζo α β hα hβ hαβ
  haveI : CharP K 2 := ringChar.of_eq hchar
  refine ggLayerOf_map_famCentralizer_of_pPower (τ := Tag.E6) (K := K) (p := 3)
    Nat.prime_three _ ?_ ?_
  · intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact ⟨1, by rw [pow_one]; exact zetaVec_pow_three_eq_one hζ _⟩
  · rw [famKernel_kgExpVec_add hζo hζ α β]
    exact isQuasisimple_rootSpan_d4 hα hβ hαβ

theorem kgAdjL3i : KGAdjL3i := by
  intro K _ _ hchar ζ hζ hζo α β hα hβ hαβ
  haveI : CharP K 2 := ringChar.of_eq hchar
  refine ggLayerOf_map_famCentralizer_of_pPower (τ := Tag.E6) (K := K) (p := 3)
    Nat.prime_three _ ?_ ?_
  · intro a ha
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact ⟨1, by rw [pow_one]; exact zetaVec_pow_three_eq_one hζ _⟩
    · exact ⟨1, by rw [pow_one]; exact zetaVec_pow_three_eq_one hζ _⟩
  · rw [famKernel_kgExpVec_pair hζo hζ hα hβ]
    exact isQuasisimple_rootSpan_a3 hα hβ hαβ


theorem isQuasisimple_rootSpan_perp {K : Type} [Field K] [Finite K] [CharP K 2]
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    IsQuasisimple (rootSpan Tag.E6 K {γ | IsRoot Tag.E6 γ ∧ iform γ β = 0}) := by
  obtain ⟨u, hu⟩ := exists_weyl_smul_a5 hβ
  rw [← hu]
  refine isQuasisimple_rootSpan_smul u (fun γ h => h.1) ?_
  have hset : {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ γ 1 = 0} = E6Pilot.a5LeviRoots := by
    rw [E6Pilot.a5LeviRoots_eq_perpRoots]
    rfl
  rw [hset, ← E6Pilot.map_subtype_a5Levi]
  exact (CFSG.IsQuasisimple.congr (Subgroup.equivMapOfInjective (E6Pilot.a5Levi K)
    (adjointGroup Tag.E6 K).subtype (adjointGroup Tag.E6 K).subtype_injective)).mp
    (E6Pilot.isQuasisimple_a5Levi (K := K))

theorem kgAdjL1 : KGAdjL1 := by
  intro K _ _ hchar ζ hζ hζo β hβ
  haveI : CharP K 2 := ringChar.of_eq hchar
  refine ggLayerOf_map_famCentralizer_of_pPower (τ := Tag.E6) (K := K) (p := 3)
    Nat.prime_three _ ?_ ?_
  · intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact ⟨1, by rw [pow_one]; exact zetaVec_pow_three_eq_one hζ _⟩
  · rw [famKernel_kgExpVec_single hζo hζ hβ]
    exact isQuasisimple_rootSpan_perp hβ

end CFSG.StandardType.KGL

end

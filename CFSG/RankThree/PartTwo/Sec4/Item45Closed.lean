module

public import CFSG.RankThree.PartTwo.Sec4.Item45
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.MSection
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.Sporadic.Bridge.MonsterModels
public import Certificates.Certificate9124
public import CFSG.Sporadic.Co2Schreier.ThirdChain
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate16018
public import Certificates.Certificate2
public import Certificates.Certificate2053
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2130
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate6006
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8026Base
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.RankThree.PartOne

open CFSG.Open CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.Existence CFSG.YGroups.Y443

section MSection

theorem simplePresentationMHasBSection_of_fM : SimplePresentationMHasBSection := by
  intro T _ _ _ _ ⟨e⟩
  have eM : T ≃* MonsterY443Derived :=
    e.trans CFSG.Blueprint.NativeSporadic.MonsterModel.y443DerivedEquivOpen
  have hsimple : IsSimpleGroup MonsterY443Derived := MulEquiv.isSimpleGroup eM.symm
  have hinj : Function.Injective fM := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (fM.ker) with h | h
    · exact h
    · exact absurd h fM_ker_ne_top
  exact exists_section_of_equiv_of_le Gmat
    (eM.trans (MulEquiv.ofBijective fM ⟨hinj, SPOR.fM_surjective⟩)) Cgen Cgen_le_Gmat Zstar phiB

end MSection

end CFSG.RankThree.PartOne

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.RankThree.PartOne

section Item45

theorem rank3II_4_5 : Item4_5 :=
  rank3II_4_5_of_bridge TCB.tcKGroupBridge sectionsForceEvenRankFour_B
    (simplePresentationM_sections_of_B_section sectionsForceEvenRankFour_B
      simplePresentationMHasBSection_of_fM)

end Item45

end CFSG.RankThree.PartTwo.Sec4

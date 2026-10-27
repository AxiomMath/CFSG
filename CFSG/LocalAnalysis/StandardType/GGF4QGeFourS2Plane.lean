module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusSingleton
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightBasic
public import CFSG.Assembly.LargeEvenDefs
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusCentralizer
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
import CFSG.GroupTheory.LocalCores.Components
import Mathlib.Tactic.Group
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
public import CFSG.RankThree.PartOne.AUTSL.Rows
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus minusIndexEquiv)

variable {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]

theorem lieModel_map_minusPairPerp_four {f : ℕ} (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {ψ : matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c) →* G}
    (hψ : Function.Injective ψ) (k : Fin (4 - 1)) :
    CFSG.Blueprint.LieModel ((minusPairPerp (by omega) b c k).map ψ) .PSU 4 2 f :=
  (lieModel_minusPairPerp_four hK hirr k).of_mulEquiv
    ((minusPairPerp _ b c k).equivMapOfInjective ψ hψ)

end CFSG.StandardType

end

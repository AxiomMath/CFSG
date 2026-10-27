module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2Proof
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofU3Inn
import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpFree
import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpMinus
import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofPlusL4
import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofPlusU4
import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusL4
import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusU4
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec21

section Certs

theorem item211ResidualLie_of_g2 (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hPG2 : KS211ExcPlusG2) (hMG2 : KS211ExcMinusG2) (hL : KS211L3PlusLinearOuter)
    (hU : KS211L3PlusUnitaryOuter) : Item211ResidualLie :=
  item211ResidualLie_of_models h45 h66 hPG2 ks211ExcPlusSp_holds ks211ExcPlusU4_holds
    ks211ExcPlusL4_holds hMG2 ks211ExcMinusSp_holds ks211ExcMinusU4_holds ks211ExcMinusL4_holds
    hL (ks211L3PlusUnitaryCore_of_outer hU)

end Certs

end CFSG.RankThree.PartTwo.Sec21

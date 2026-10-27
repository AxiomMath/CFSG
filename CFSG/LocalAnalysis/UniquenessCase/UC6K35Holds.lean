module

public import CFSG.LieType.SeitzGeneration.InnerExHolds
public import CFSG.LieType.SeitzGeneration.ConsumerEx
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MonsterTargets
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorusFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutElemRank
public import CFSG.LieType.SeitzGeneration.SpF2.Main
public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
public import CFSG.LieType.SeitzGeneration.OmegaF2.Plus
public import CFSG.LieType.SeitzGeneration.OmegaF2.Minus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuterAssembly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

section SmallIdent


theorem kFactSmallIdent_holds
    : CFSG.AGLEmbedding.KFactSmallIdent :=
  CFSG.LieType.SeitzGeneration.kFactSmallIdent_of_seitzEx_of_rows
    CFSG.LieType.SeitzGeneration.kFactSeitzRankTwoInnerEx_holds
    CFSG.AGLEmbedding.sporGammaOneAt_HS_five CFSG.AGLEmbedding.sporGammaOneAt_B_seven
    (CFSG.AGLEmbedding.smallIdentSporAt_M_of_betaData
      CFSG.AGLEmbedding.Norton.OrdinaryProofs.monsterBetaData_of_thirteen_cubic
      (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M) CFSG.Milestones.fam_m_finiteness
      CFSG.AGLEmbedding.Norton.sporGammaOneAt_M_eleven_holds
      CFSG.AGLEmbedding.Norton.sporGammaOneAt_M_thirteen_holds)

end SmallIdent

section OneLie


theorem kFactOneLieIdent_holds
    : CFSG.AGLEmbedding.KFactOneLieIdent :=
  CFSG.LieType.SeitzGeneration.kFactOneLieIdent_of_seitzEx
    CFSG.LieType.SeitzGeneration.kFactSeitzRankTwoInnerEx_holds
    (CFSG.AGLEmbedding.oneLieIdentSporAt_M_of_betaData
      CFSG.AGLEmbedding.Norton.OrdinaryProofs.monsterBetaData_of_thirteen_cubic
      (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M))

theorem kFactOneLieTorus_holds
    : CFSG.AGLEmbedding.KFactOneLieTorus :=
  CFSG.AGLEmbedding.kFactOneLieTorus_of kFactOneLieIdent_holds
    CFSG.AGLEmbedding.kFactUnitarySylowStructure CFSG.AGLEmbedding.kFactUnitarySylowCenterTorus
    CFSG.AGLEmbedding.kFactUnitaryTorusPPD CFSG.AGLEmbedding.kFactUnitaryBorelMaximal
    CFSG.AGLEmbedding.kFactUnitarySylowNormalizerSolvable CFSG.AGLEmbedding.kFactUnitaryAutElemRank
    CFSG.AGLEmbedding.kFactReeSylowCenterTorus CFSG.AGLEmbedding.kFactReeBorelMaximal
    CFSG.AGLEmbedding.kFactReeSylowNormalizerSolvable CFSG.AGLEmbedding.kFactReeAutElemRank

end OneLie

section CyclicOuter


theorem stronglyEmbeddedCyclicOuter_holds :
    CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter.stronglyEmbeddedCyclicOuter_of_seitzOuterLowN
    (CFSG.HardMathSupport.Malle.SeitzCube.innerEx_lowN_of_pairs_aniso
      CFSG.LieType.SeitzGeneration.subfieldPairSpF2_holds
      CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds
      (CFSG.LieType.SeitzGeneration.subfieldPairOmegaPlusChar2_of_F2
        CFSG.LieType.SeitzGeneration.subfieldPairOmegaPlusF2_holds)
      (CFSG.LieType.SeitzGeneration.subfieldPairOmegaMinusChar2_of_F2
        CFSG.LieType.SeitzGeneration.subfieldPairOmegaMinusF2_holds)
      CFSG.LieType.SeitzGeneration.seitzExcAnisotropicNotG2ThreePlus_holds
      CFSG.LieType.SeitzGeneration.seitzExcOuterNarrow_holds).2.2

end CyclicOuter

end CFSG.LocalAnalysis.UniquenessCase.UCK

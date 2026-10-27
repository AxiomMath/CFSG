module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwelve
public import CFSG.LocalAnalysis.StandardType.GGSpFrameType
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallASpLift
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGMark
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGConfig
public import CFSG.LocalAnalysis.StandardType.GGSpFrameRank
public import CFSG.LocalAnalysis.StandardType.GGSpJoinMaxElemSp
public import CFSG.LocalAnalysis.StandardType.GGSpFrameLine
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem ggStdSubPrimeInput_of_round12 (hTE6 : GGTableBTwE6Round12)
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (hsR : GGStdSubSmallInputOn GGStdSubSmallRest4Label) : GGStdSubPrimeInput :=
  have ha₀ : GGLNoncyclicInput := ggLNoncyclicInput_holds
  have ha : GGBstarInput := ggBstarInput_of_round3 ha₀ ggBstarDeltaUnitaryInput_holds
    ggBstarInputOn_rest3_unitary (ggBstarInputOn_orthRest_of_odd ha₀ ggOrthRestBstarOddInput_holds)
    (ggBstarInputOn_other_of_rest4
      (ggBstarInputOn_rest4_of_round6 hSR (ggBstarInputOn_round6_of_round12 hTE6)))
  have hs : GGStdSubSmallInput :=
    ggStdSubSmallInput_of_round3 ggStdSubTwoTorus_symplectic_of_card
      (ggStdSubSmallInputOn_rest_of_rest2 (ggStdSubSmallInputOn_rest2_of_rest4 hSR hsR))
  ggStdSubPrimeInput_of_small ha hs

end CFSG.StandardType

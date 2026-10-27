module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveCommKnown
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGRound12

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem ggSixPCompRootCommInput_of_knownInputs_round12 (h : GGSixRootCommKnown ∧ GGOutTwoCommInner ∧
    GGSixJNotA6Input)
    (hTE6 : GGTableBTwE6Round12) (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (hsR : GGStdSubSmallInputOn GGStdSubSmallRest4Label) : GGSixPCompRootCommInput :=
  have hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog :=
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  ggSixPCompRootCommInput_of_knownInputs h
    (ggInnerDiagMarkingInput_of_E6 fun t ht => by
      rcases ht with rfl | rfl
      exacts [ggInnerDiagMarkingAt_E6, ggInnerDiagMarkingAt_twistedE6])
    (ggPumpupInput_of_lBalance (ggLBalanceInput_of_catalogueSchreier hSch))
    (ggStdSubPrimeInput_of_round12 hTE6 hSR hsR) ggLNoncyclicInput_holds

end CFSG.StandardType

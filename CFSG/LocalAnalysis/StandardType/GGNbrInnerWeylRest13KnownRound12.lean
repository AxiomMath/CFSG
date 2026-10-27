module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Known
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGRound12

public section

namespace CFSG.StandardType

theorem ggNbrInnerWeylOn_rest13_of_known_round12 (hTE6 : GGTableBTwE6Round12)
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (hsR : GGStdSubSmallInputOn GGStdSubSmallRest4Label) (hG : GGNbrGraphInput)
    (hKG : GGNbrWeylKGInput) (hOther : GGNbrInnerWeylOn GGNbrWeylFieldOtherLabel)
    (hRes : GGNbrInnerWeylOn GGNbrWeylResidualLabel) :
    GGNbrInnerWeylOn GGNbrWeylRest13Label :=
  ggNbrInnerWeylOn_rest13_of_known
    (ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds)
    (ggStdSubPrimeInput_of_round12 hTE6 hSR hsR) hG hKG hOther hRes

end CFSG.StandardType

end

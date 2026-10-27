module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Main
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45SzAut
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSp
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45InspHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEvenHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Proved

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

set_option linter.unusedSectionVars false


theorem k45Odd_holds
    : K45Odd :=
  k45Odd_of_pieces RankThreeTheoremC.SmallRankE3.kFactSuzukiThreeFree_holds szOrder3Aut_holds
    pairSp_holds inspPairShape_holds

theorem k462_holds
    : K462 :=
  k462_of_open k45Odd_holds

end CFSG.LocalAnalysis.UniquenessCase.UCK

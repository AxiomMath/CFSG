module

public import CFSG.RankThree.GF2n.Smith81.InspK1NSL
public import CFSG.RankThree.GF2n.Smith81.InspKOmegaFour
public import CFSG.RankThree.GF2n.Smith81.InspOrthSmall

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.CGT.Timmesfeld75

theorem smith219OrthInspection_of_K (h23 : Smith23E1LgenStatement)
    (h212O : Smith212OrthCoreStatement) : Smith219OrthInspectionStatement :=
  smith219OrthInspection_of
    (smith219OrthSmall_of h23 h212O k1NSL_holds k2PSL_holds kCOmega_holds kCOmegaFour_holds)
    h212O k1NSL_holds k2PSL_holds kCOmega_holds

end CFSG.RankThree.GF2n.Smith81.Insp

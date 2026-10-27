module

public import CFSG.RankThree.GF2n.Smith81.S81Lane28

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem smith216E_of_28 (hN : Smith212ENonfusedStatement) (h213 : Smith213EStatement)
    (hCount : Smith216ECountStatement) (h28 : Smith28EStatement) : Smith216EStatement :=
  smith216E_of_nonfused hN h213 hCount (smith216EOdd_of_28_nonfused h28 hN h213 hCount)

end CFSG.RankThree.GF2n.Smith81

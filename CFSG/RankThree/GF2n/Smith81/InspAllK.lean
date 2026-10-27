module

public import CFSG.RankThree.GF2n.Smith81.InspLin
public import CFSG.RankThree.GF2n.Smith81.InspK1NSL
public import CFSG.RankThree.GF2n.Smith81.InspKPSp
public import CFSG.RankThree.GF2n.Smith81.InspKOmega
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.CGT.Timmesfeld75

theorem linInspect_holds : LinInspectStatement :=
  linInspect_of k1NSL_holds k2PSL_holds k2PSp_holds kCOmega_holds

end CFSG.RankThree.GF2n.Smith81.Insp

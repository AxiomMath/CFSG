module

public import CFSG.RankThree.PartTwo.Sec4.Census.TwoCoverCensusResidual
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverM11
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverM23
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverJ1
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverJ3
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverON

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

section Residual

theorem sporadicTwoCoverResidual : SporadicTwoCoverResidual where
  m11 := noRankThreeTwoCover_m11
  m23 := noRankThreeTwoCover_m23
  j1 := noRankThreeTwoCover_j1
  j3 := noRankThreeTwoCover_j3
  onan := noRankThreeTwoCover_on

end Residual

end CFSG.RankThree.PartTwo.Sec4.Census

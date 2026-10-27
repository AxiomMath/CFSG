module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FFinal
public import CFSG.RankThree.PartTwo.Sec8.Hering418FU4Odd

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

section Done


theorem kF418Faithful_of_hAS (h46 : Sec4.Item4_6) (h47 : Sec4.Item4_7)
    (hAS : KF418ModelAltSpor) : KF418Faithful :=
  kF418Faithful_of_hU4 h46 h47 hAS kF418ModelOn47_uFourSix

theorem item418Theta_of_hAS (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (h47 : Sec4.Item4_7)
    (hAS : KF418ModelAltSpor) : Item418Theta :=
  item418Theta_of h45 (kF418Faithful_of_hAS h46 h47 hAS)

end Done

end CFSG.RankThree.PartTwo.Sec8.Hering418

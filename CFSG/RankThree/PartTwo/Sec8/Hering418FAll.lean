module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FLin
public import CFSG.RankThree.PartTwo.Sec8.Hering418FU

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

section All

theorem kF418Faithful_of_remaining47 (h46 : Sec4.Item4_6) (h47 : Sec4.Item4_7)
    (hAS : CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418.KF418ModelAltSpor)
    (hD4 : KF418ModelOn (fun X _ => IsTrialityD4Six X))
    (hrank : Sec21.TwistedF4EvenThreeRankTwo)
    (hU4 : KF418ModelOn47 (fun X _ => IsUFourSix X)) : KF418Faithful :=
  kF418Faithful_of_families47' h46 h47 hAS kF418ModelOn_lThreeSixEven kF418ModelOn_uThreeSixOdd
    kF418ModelOn_slThreeSixEven kF418ModelOn_suThreeSixOdd hD4 hrank hU4

end All

end CFSG.RankThree.PartTwo.Sec8.Hering418

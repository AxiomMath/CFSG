module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem s2a_holds : S2a := by
  unfold S2a
  intro G _ _ c L L' hL hL' hne l hl l' hl'
  exact CFSG.RankThree.PartTwo.Sec10.commutator_mem_theta_of_ne hL hL' hne hl hl'

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b

module

public import CFSG.RankThree.GF2n.Tim81.Sec8.RankOne
public import CFSG.RankThree.GF2n.Tim81.Sec8.Parabolic
public import CFSG.RankThree.GF2n.Tim81.Sec8.SmallRank

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.RankThree.PartOne

theorem sec8Statement_of_pushingUpCorollary
    (hPU : PushingUpCorollary) : Sec8Statement :=
  sec8Statement_of_pushingUp hPU sec8RankOneStatement sec8L3Statement sec8Sp4Statement
    sec8SmallRankStatement

end CFSG.RankThree.GF2n.Tim81

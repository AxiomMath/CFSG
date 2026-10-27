module

public import CFSG.RankThree.PartTwo.Sec6.BThreeFromLBalance
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.RankThree.PartTwo.Sec6


theorem gwlBalanceStatement_holds
    : GWLBalanceStatement :=
  fun X _ _ hK p hp P hP => CFSG.Milestones.cl_lit_gorenstein_walter_l_balance X hK p hp P hP

end CFSG.RankThree.PartTwo.Sec6

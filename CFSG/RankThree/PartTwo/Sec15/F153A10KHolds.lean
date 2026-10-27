module

public import CFSG.RankThree.PartTwo.Sec15.F153A10KAut
public import CFSG.RankThree.PartTwo.Sec15.F153A10KPerm
public import CFSG.RankThree.PartTwo.Sec15.F153A10KMain

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153A10K

theorem a10NoV4Offender_holds : CFSG.RankThree.PartTwo.Sec15.F153.A10NoV4Offender :=
  a10NoV4Offender_of p2Stmt_holds p4Stmt_holds
    (fun _ _ _ hW X h => not_twentyfive_dvd_card hW X h)
    (fun _ _ _ hW X h => not_five_dvd_card hW X h)

end CFSG.RankThree.PartTwo.Sec15.F153A10K

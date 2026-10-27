module

public import CFSG.RankThree.PartTwo.Sec13.Item134Unconditional
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3WR
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3A6
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3A7
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3G23
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3M22
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3U43
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L3Main
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125L3
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125J3
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125McL
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3L125ON
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Holds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo


theorem step155NoG28WR_of_k9
    (hK9 : Res3K9) : Step155NoG28WR :=
  step155NoG28WR_of_res3 item134_holds item135_holds Sec11.Close.closed_sec4Item4_1LargePrime
    Sec11.Close.closed_sec4Item4_1ThreeCover
    (Sec4.Item41Narrow.item4_1LargeAll_of_griess
      ComponentClassification.TBLit.griessMultipliersAllModels_holds)
    Sec4.rank3II_4_5 Sec11.Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15
    KFacts.KS14.sporadicModels131 hK9 (res3NoDatum_of Sec11.Close.closed_sec4Item4_3
        res3NoDatumL3Two_holds res3NoDatumL3Odd_holds res3NoDatumA6_holds res3NoDatumA7_holds
        res3NoDatumG23_holds res3NoDatumU43_holds res3NoDatumM22_holds res3NoDatumJ3_holds
        res3NoDatumMcL_holds res3NoDatumON_holds)

theorem step155NoG28WR_holds
    : Step155NoG28WR :=
  step155NoG28WR_of_k9 res3K9_holds

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3

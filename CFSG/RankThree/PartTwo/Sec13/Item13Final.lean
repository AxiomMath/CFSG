module

public import CFSG.RankThree.PartTwo.Sec13.Item132
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem rank3II_13_2_of (h131 : Item131) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) :
    Item132 :=
  rank3II_13_2_of_inputs h131 sporadicModels131 slTwoCenter (item13SetupAt_of h422 h45)
    k410NotInverted (notSLTwoOfHypT_of h131 sporadicModels131)

end CFSG.RankThree.PartTwo.Sec13

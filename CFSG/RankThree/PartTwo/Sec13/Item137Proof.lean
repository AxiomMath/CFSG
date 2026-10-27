module

public import CFSG.RankThree.PartTwo.Sec13.Item137NormLe
import CFSG.RankThree.PartTwo.Sec13.Item13Final
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local

public section

namespace CFSG.RankThree.PartTwo.Sec13

theorem item137_of
    (h131 : Item131) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h13S : Sec17.Item13Setup) (hMove : Item137Move) : Item137 :=
  rank3II_13_7_of_inputs h131 (rank3II_13_2_of h131 h422 h45) h13S sporadicModels131
    Sec4.Sporadic.rank3II_4_14_local (fun X _ h => Toolkit.m12ThreeLocalData X h) hMove

end CFSG.RankThree.PartTwo.Sec13

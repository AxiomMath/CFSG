module

public import CFSG.RankThree.PartTwo.Sec17.Item1730Chosen
import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

theorem step1730Chosen_of_j2 (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hJ2 : KFacts.KS17J2NotList) : Step1730Chosen :=
  step1730Chosen_of h131 hspor hSLC h134 h48 h415 CFSG.Sporadic.J2.isSimpleGroup_J2 hJ2

end CFSG.RankThree.PartTwo.Sec17


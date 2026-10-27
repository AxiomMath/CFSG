module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155RChar
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQ0
import CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15

theorem kFSubL3 : KFSubL3 :=
  Ronan155DiamondL3.kfSubL3_holds

theorem step155CasesTwoNHJWR_of_route (hY4 : Y4LThreePiNHJR) (h152 : Item152R)
    (h153 : Item153MainR) (hgrow : Step155GrowWR) (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS14) (hYQ : Step155YQ0WR) (hPJQ : Step155PJQ0WR) :
    Step155CasesTwoNHJWR :=
  step155CasesTwoNHJWR_of_kf hY4 h152 h153 hgrow h146 h1444 hbot hYQ hPJQ kFSubL3

theorem step155CasesTwoNHJWR_of_route' (hY4 : Y4LThreePiNHJR) (h152 : Item152R)
    (h153 : Item153MainR) (hgrow : Step155GrowWR) (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) (hYQ : Step155YQ0HypWR)
    (hPJQ : Step155PJQ0HypWR) : Step155CasesTwoNHJWR :=
  step155CasesTwoNHJWR_of_route hY4 h152 h153 hgrow h146 h1444 hbot (step155YQ0WR_of h142 hYQ)
    (step155PJQ0WR_of h142 hPJQ)

end CFSG.RankThree.PartTwo.Sec15.Ronan155R

module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WField
public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCore
import CFSG.RankThree.PartTwo.Sec14.Wales1411WJ2

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

theorem claim1411NonsolvWPointL3FieldR_of_tori
    (h131 : Item131)
    (h142 : Item142AllS14) (hbot : Item145BotS14) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (hKL : KL3HessTori) (hHJ : Claim1411NonsolvWPointHJConfR) :
    Claim1411NonsolvWPointL3FieldR :=
  claim1411NonsolvWPointL3FieldR_of_cases
    (claim1411NonsolvWPointL3FieldOmegaR_of_tori h131 h142 hbot h422 h45 hKL) hHJ

theorem item1411_1R_of_hjconf
    (h131 : Item131) (h142 : Item142AllS14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (hKL : KL3HessTori)
    (hHJ : Claim1411NonsolvWPointHJConfR) : Item1411_1R :=
  item1411_1R_of_field h131 h142 h146 hbot Wales1411W.etrans2_J2 (kl3HessETrans2_of_tori hKL)
    (claim1411NonsolvWPointL3FieldR_of_tori h131 h142 hbot h422 h45 hKL hHJ)

theorem item1411_1R_of_hjcore
    (h131 : Item131) (h142 : Item142AllS14) (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hKL : KL3HessTori) (hcore : Claim1411HJConfCoreR) : Item1411_1R :=
  item1411_1R_of_hjconf h131 h142 h146 hbot h422 h45 hKL
    (claim1411NonsolvWPointHJConfR_of_core h142 hbot Wales1411W.etrans2_J2 h143 h134 h48 hcore)

theorem item1411_1R_of_hjkfact
    (h131 : Item131) (h142 : Item142AllS14) (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14)
    (h148 : Item148R) (hbot : Item145BotS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (hKL : KL3HessTori) (hKF : KS1411HJCore) :
    Item1411_1R :=
  item1411_1R_of_hjcore h131 h142 h143 h146 hbot h134 h48 h422 h45 hKL
    (claim1411HJConfCoreR_of_kfact h148 h143 h134 h48 hbot hKF)

end CFSG.RankThree.PartTwo.Sec14

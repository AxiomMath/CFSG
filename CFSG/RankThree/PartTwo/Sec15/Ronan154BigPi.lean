module

public import CFSG.RankThree.PartTwo.Sec15.Wales154L3Five
public import CFSG.RankThree.PartTwo.Sec15.Item154PiProof
import CFSG.RankThree.PartTwo.Sec4.Item422Holds
public import CFSG.RankThree.PartTwo.Sec14.Item1411_3RHolds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan154Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

section Pi


theorem item154PiR_of_item159R
    (h159 : Item159R) : Item154PiR := by
  obtain ⟨-, h48, -, -, -, -, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  have h148 : Item148R := Ronan148M.item148R_holds
  have hbot : Item145BotS14 := Ronan149.item145BotS14_holds
  have h131 : Item131 := rank3II_13_1_holds
  have h422 := item4_22_holds
  have h45 := Sec4.rank3II_4_5
  have h414 := Sec4.Sporadic.rank3II_4_14_local
  have h415 := Sec4.Sporadic.rank3II_4_15
  have hBr : Sec16.Step169TwoBridge := Sec16.step169TwoBridge_of
    (item135SimpleReduce_narrow
      (item4_4Types135_of_item4_4 Sec4.Census.rank3II_4_4_of_griess_noItem41)
      (ks135TwoRank_of_cover ks135TwoRankCover h414 h415) KFacts.KS14.sporadicModels131
      h414 h415)
  exact item154PiR_of_proper h148 hbot
    (Wales154.item154ProperR_of_route h148 h134 h48 hbot (item142R_of_wired item142AllS14_holds)
      LiebeckClosed.item158Y0R_holds (item13SetupAt_of h422 h45) (rank3II_13_3_of h131 h422 h45)
      h159 item1510R_holds hBr)
    Ronan155Y.y4LThreePiNHJR_holds

end Pi

end CFSG.RankThree.PartTwo.Sec15.Ronan154Big

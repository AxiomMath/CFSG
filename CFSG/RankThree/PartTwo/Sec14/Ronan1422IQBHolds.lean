module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB
public import CFSG.RankThree.PartTwo.Sec15.Gagen148FourKHolds
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofRoute
public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaM22

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13


theorem step1422IQBLayerR_holds
    : Step1422IQBLayerR := by
  obtain ⟨h45, -, -, -, h46, -, -, h131, -, -, h142All⟩ := Ronan148M.closedInputs
  exact step1422IQBLayerR_of h131 h45 h46 KFacts.kpSz
    (item1413CR_of_res7 h131 h142All Ronan148M.concl142S14_holds
      Sec15.Proof148FourK.item146S14_holds Ronan149.item145BotS14_holds)
    Sec21.Holder214Theta.m22E9NoInvol_holds

end CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB

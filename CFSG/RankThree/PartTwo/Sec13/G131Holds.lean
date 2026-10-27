module

public import CFSG.RankThree.PartTwo.Sec13.Item131Narrow
public import CFSG.RankThree.PartTwo.Sec13.Item13ResProofW
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bMain
public import CFSG.RankThree.PartTwo.Sec12.Item128Assembly

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem rank3II_13_1_holds
    : Item131 :=
  have h45 : Sec4.Item4_5 := Sec11.Close.closed_sec4Item4_5
  have h422 : Sec4.Item4_22 :=
    KFacts.rank3II_4_22_of_items_noItem41 Sec11.Close.closed_sec4Item4_5
      Sec11.Close.closed_tBLitGriessMultipliersAllModels Sec11.Close.closed_sec4Item4_3
  have h128 : Sec12.Item128BarAt :=
    Sec12.item128BarAt_of_inputs (Sec11.item1134E27N_of Sec11.Close.narrow_sec9Hyp91SmallNever)
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hU : Step131bSLTwoInEU :=
    step131bSLTwoInEU_of_odd
      (RonanStep131b.step131bSLTwoInEUOdd_of_item131a rank3II_13_1a_narrow)
  rank3II_13_1_narrow
    (item131b_of_item45 h128 h422 h45 (step131bSLTwo_of_U h128 h422 h45 h415 hU))

end CFSG.RankThree.PartTwo.Sec13

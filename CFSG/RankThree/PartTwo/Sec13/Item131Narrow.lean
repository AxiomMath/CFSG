module

public import CFSG.RankThree.PartTwo.Sec11.Item11CloseNarrow
public import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofSLThree
public import CFSG.RankThree.PartTwo.Sec13.Item131aSmall
public import CFSG.RankThree.PartTwo.Sec13.Item131Assembly

public section

namespace CFSG.RankThree.PartTwo.Sec13

section FromItem41


theorem rank3II_13_1a_narrow
    : Item131a :=
  rank3II_13_1a_of_item1134E27N Sec11.Close.closed_sec4Item4_23
    (KFacts.rank3II_4_22_of_items_noItem41 Sec11.Close.closed_sec4Item4_5
      Sec11.Close.closed_tBLitGriessMultipliersAllModels Sec11.Close.closed_sec4Item4_3)
    Sec11.Close.closed_sec4Item4_5
    (ks131AlphaInvolutionCentral_of_item4_6 Sec11.Close.closed_sec4Item4_6)
    (Sec11.item1134E27N_of Sec11.Close.narrow_sec9Hyp91SmallNever)

theorem rank3II_13_1_narrow
    (h131b : Item131b) : Item131 :=
  rank3II_13_1_of_parts rank3II_13_1a_narrow h131b

end FromItem41

end CFSG.RankThree.PartTwo.Sec13

module

public import CFSG.RankThree.PartTwo.Sec4.T444.Part1
public import CFSG.RankThree.PartTwo.Sec4.T444.Step450
public import CFSG.RankThree.PartTwo.Sec4.T444.Step453
public import CFSG.RankThree.PartTwo.KFacts.KS44Sz

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem rank3II_4_50_of_item4_47 (h447 : Item4_47) : Item4_50 :=
  rank3II_4_50_of KFacts.kpSz h447

theorem rank3II_4_44_1_of_inputs (h434 : Item4_34Sec) (h447 : Item4_47) (h45 : Item4_5)
    (h44 : Item4_4) (hres : Item4_52Residual) (hmult : KFacts.L34CenterThreePrimeTwo) :
    Item4_44_1 :=
  have h452 := rank3II_4_52_of h434 h45 h44 hres
  rank3II_4_44_1_of (rank3II_4_50_of_item4_47 h447) h452 (rank3II_4_53_of h434 h45 h452 hmult)

theorem rank3II_4_44_1_of_griess (h434 : Item4_34Sec) (h447 : Item4_47) (h45 : Item4_5)
    (h44 : Item4_4) (hres : Item4_52Residual)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : Item4_44_1 :=
  rank3II_4_44_1_of_inputs h434 h447 h45 h44 hres
    (KFacts.KS44.l34CenterThreePrimeTwo_of_griess hGA)

end CFSG.RankThree.PartTwo.Sec4

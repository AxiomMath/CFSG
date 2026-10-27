module

public import CFSG.RankThree.PartTwo.Sec21.Hering2125RCases
public import CFSG.RankThree.PartTwo.Sec11.Item11CloseNarrow

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

theorem item2125Cases
    : Item2125Cases :=
  item2125Cases_of Sec4.rank3II_4_5
    (let hGA := CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
     Sec4.Census.rank3II_4_6_of_griess_narrow41
      (Sec4.Item41Narrow.item4_1LargePrime_of_griess hGA)
      (Sec4.Item41Narrow.item4_1ThreeCover_of_griess hGA) hGA
      (Sec4.Census.coverCenterThreeRest_of hGA))
    Sec11.kFact1118Triality46 Sec11.item4_24M_holds Sec11.item1134E27N_of_standing_narrow
    (item1134E27ST_of Sec11.Close.narrow_sec11Hyp91Never)

end CFSG.RankThree.PartTwo.Sec21.Hering2125

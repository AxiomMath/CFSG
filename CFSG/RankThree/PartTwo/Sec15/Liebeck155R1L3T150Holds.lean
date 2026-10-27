module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150Main
public import CFSG.RankThree.PartTwo.Sec4.Item41ScopeProofAll
public import CFSG.RankThree.PartTwo.Sec14.Ronan149Holds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem res1Thm150b_l3_holds
    {P : ∀ (Y : Type) [Group Y], Prop} :
    Sylow155R1.Res1Thm150b GagenL3.Res1L3Q P :=
  res1Thm150b_l3 Sec4.diag_item41LargePrime_holds Sec11.Close.closed_sec4Item4_1ThreeCover
    Sec4.Census.rank3II_4_4_of_griess_noItem41
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    Sec11.Close.closed_sec4Item4_5 Sec11.Close.closed_sec4Item4_8 Sec14.Ronan149.item149S14_holds

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

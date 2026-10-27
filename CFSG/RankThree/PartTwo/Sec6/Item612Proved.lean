module

public import CFSG.RankThree.PartTwo.Sec4.Item45Closed
public import CFSG.RankThree.PartTwo.Sec4.Item48Proof
public import CFSG.RankThree.PartTwo.Sec4.Item49Proved
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreClosed
public import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndexProof
public import CFSG.RankThree.PartTwo.Sec6.Item612UsedOf

public section

namespace CFSG.RankThree.PartTwo.Sec6

theorem rank3II_6_12_sec21_closed
    : CFSG.RankThree.PartTwo.Sec21.Item612 :=
  CFSG.RankThree.PartTwo.Sec6.rank3II_6_12_sec21_of_used CFSG.RankThree.PartTwo.Sec4.rank3II_4_5
    (CFSG.RankThree.PartTwo.Sec4.rank3II_4_8_of CFSG.RankThree.PartTwo.Sec4.rank3II_4_5)
    CFSG.RankThree.PartTwo.Sec4.rank3II_4_9
    (CFSG.RankThree.PartTwo.KFacts.ks6OuterIndex_of
      (CFSG.RankThree.PartTwo.Sec4.rank3II_4_7W_of (Sec4.Census.rank3II_4_6_of_griess_noItem41
          ComponentClassification.TBLit.griessMultipliersAllModels_holds
          (Sec4.Census.coverCenterThreeRest_of
              ComponentClassification.TBLit.griessMultipliersAllModels_holds))))

end CFSG.RankThree.PartTwo.Sec6

module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofThree
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofB
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section LThreeCerts

theorem item2130TypesLThree_of_res6 (h41 : Sec4.Item4_1LargePrime)
    (hEven : Item2130CaseBEven) : Item2130TypesLThree :=
  item2130TypesLThree_of h41 (item2130CaseB_of hEven) item2130CaseTypeThree_holds

end LThreeCerts

end CFSG.RankThree.PartTwo.Sec21

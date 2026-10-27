module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLProof
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.RankThree.PartTwo.Sec4.T444.Gap452Proof
public import CFSG.RankThree.PartTwo.Sec4.Item4442Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem item4_44_3SL_of
    (h434 : Item4_34Sec) (h45 : Item4_5) : Item4_44_3SL :=
  item4_44_3SL_of_inputs h434 h45 (rank3II_4_44_2_of h45 h434) KFacts.kpSz
    PartOne.TCB.schreierFor_inCatalog_holds rank3II_4_52_residual KFacts.l34CenterThreePrimeTwo

end CFSG.RankThree.PartTwo.Sec4.Item4443SL

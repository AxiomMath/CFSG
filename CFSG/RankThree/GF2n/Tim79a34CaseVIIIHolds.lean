module

public import CFSG.RankThree.GF2n.Tim79a34CaseVIII
public import CFSG.RankThree.GF2n.Tim79a34GammaSteps
public import CFSG.RankThree.GF2n.Tim79a34StrothHyp

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

theorem ntCaseVIIIStatement_holds : NTCaseVIIIStatement := by
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  have h11a : Lemma11aStatement := lemma11a_holds spRadFactsStatement_holds
  have h11b : Lemma11bStatement := lemma11b_holds hN h11a spRadFactsStatement_holds
  have h11c : Lemma11cStatement := lemma11c_holds spRadFactsStatement_holds h11a
  exact ntCaseVIII_holds h11a h11b h11c lemma12Statement_holds
    (ntStrothHyp_holds h11a h11b lemma12Statement_holds)

end CFSG.RankThree.GF2n.Tim79a

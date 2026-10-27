module

public import CFSG.RankThree.GF2n.Tim79a34Gamma

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

theorem lemma12Statement_holds : Lemma12Statement := by
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  have h11a : Lemma11aStatement := lemma11a_holds spRadFactsStatement_holds
  exact lemma12_holds (sec34IW_holds hN spRadFactsStatement_holds commPairingStatement_holds)
    Gamma.sec34GammaStatement_holds h11a (lemma11b_holds hN h11a spRadFactsStatement_holds)
    (lemma11c_holds spRadFactsStatement_holds h11a)

end CFSG.RankThree.GF2n.Tim79a

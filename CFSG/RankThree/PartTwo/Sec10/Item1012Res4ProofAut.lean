module

public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofStatements
public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL364
public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.TripleCover

public section

namespace CFSG.RankThree.PartTwo.Sec10

theorem ks1012AutHyp_holds : KS1012AutHyp := by
  intro Q _ _ hq hQ F hF
  rcases hQ with ⟨K, _, _, ⟨hcard, -, ⟨e⟩⟩ | ⟨-, hmod, -⟩⟩ | h |
      ⟨K, _, _, ⟨hcard, -, ⟨e⟩⟩ | ⟨-, hmod, -⟩⟩
  · exact KS1012AutHyp.ks1012AutHyp_sl34_of_mulEquiv hcard Q e F hF
  · norm_num at hmod
  · exact KS1012AutHyp.ks1012AutHyp_tripleCover Q hq h F hF
  · exact KS1012AutHyp.ks1012AutHyp_sl364_of_mulEquiv hcard Q e F hF
  · norm_num at hmod

end CFSG.RankThree.PartTwo.Sec10

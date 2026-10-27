module

public import CFSG.RankThree.GF2n.Tim79a34ParrottHyp
public import CFSG.RankThree.GF2n.Tim79a34ParrottCases
public import CFSG.RankThree.GF2n.Tim79a34OddCore

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

theorem ntCaseV_holds (hH : NTStrothHypStatement) (h11a : Lemma11aStatement)
    (h11b : Lemma11bStatement) (h12 : Lemma12Statement) (h13 : Lemma13Statement) :
    NTCaseVStatement := by
  intro hP hO hFi G _ _ M V Q P H n Φ ψ a T cfg w hw hV
  rcases hP G cfg.aG (parrottHyp_of_caseV hO hH h11a h11b h12 cfg w hw hV) with h | h | h
  · exact parrott_odd_false h12 cfg h
  · exact parrottCaseII_false cfg h
  · exact fi22_false hFi h11a h12 h13 cfg w hw hV h

end CFSG.RankThree.GF2n.Tim79a

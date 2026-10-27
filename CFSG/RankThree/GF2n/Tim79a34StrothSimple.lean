module

public import CFSG.RankThree.GF2n.Tim79a34StrothCasesA
public import CFSG.RankThree.GF2n.Tim79a34StrothCasesB

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

theorem ntStrothSimple_holds (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (h12 : Lemma12Statement) (h13 : Lemma13Statement) : NTStrothSimpleStatement := by
  intro G _ _ M V Q P H n Φ ψ a T cfg w hw
  exact ⟨strothCaseI_false h11a h11b h12 cfg, strothCaseII_false h11b h12 h13 cfg w,
    strothCaseIII_false cfg w hw, strothCaseIV_false cfg w hw,
    strothCaseVI_false h12 h11b cfg w, strothCaseVII_false h11b h12 cfg w⟩

end CFSG.RankThree.GF2n.Tim79a

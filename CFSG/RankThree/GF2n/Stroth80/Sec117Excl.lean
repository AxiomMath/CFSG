module

public import CFSG.RankThree.GF2n.Stroth80.Sec117D4
public import CFSG.RankThree.GF2n.Stroth80.Sec117En
public import CFSG.RankThree.GF2n.Stroth80.Sec117F4
public import CFSG.RankThree.GF2n.Stroth80.Sec117G2
public import CFSG.RankThree.GF2n.Stroth80.Sec117SU
public import CFSG.RankThree.GF2n.Stroth80.Sec117Sz
public import CFSG.RankThree.GF2n.Stroth80.Sec117TwE6
public import CFSG.RankThree.GF2n.Stroth80.Sec117U3
import CFSG.RankThree.GF2n.Stroth80.Sec117F4TwoFacts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem stroth117Excl_holds :
    Stroth117ExclStatement := by
  rintro G _ _ M Q Z B _ hc n hw hn ha2 ⟨t, m, x, ht, hX⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨rfl, rfl | hm⟩
  · exact hc.not_lieModel_G2_xbarMod hw hn ha2 hX
  · exact hc.not_lieModel_trialityD4_xbarMod hw hn ha2 hX
  · exact hc.not_lieModel_F4_xbarMod f4ExclStatement_holds f4GenStatement_holds ha2 hX
  · exact hc.not_lieModel_E6_xbarMod hw hn ha2 hX
  · exact hc.not_lieModel_E7_xbarMod hw hn ha2 hX
  · exact hc.not_lieModel_E8_xbarMod hw hn ha2 hX
  · exact hc.not_lieModel_twistedE6_xbarMod hw hn ha2 hX
  · exact hc.not_lieModel_twistedB2_xbarMod hw hn ha2 hX
  · exact hc.not_lieModel_psu3_xbarMod hw hn ha2 hX
  · exact hc.not_lieModel_psu_xbarMod hw hn ha2 hm hX

end CFSG.RankThree.GF2n.Stroth80

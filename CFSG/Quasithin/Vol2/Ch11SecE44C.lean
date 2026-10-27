module

public import CFSG.Quasithin.Vol2.Ch11SecD553
public import CFSG.Quasithin.Vol2.Ch11SecBNPMainS
public import CFSG.Quasithin.Vol2.Ch11SecE44S

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem stmt11_4_4_of_p778S (hp778 : SecB.AS_p778_nParamS) (h331 : Stmt3_3_1)
    (h44S : Stmt11_4_4S) : Stmt11_4_4 := by
  intro G _ _ T L I n V₁ h hV₁ hK z hz hz1 H hH hHz
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hlie := h44S G T L I n V₁ h hV₁ hK z hz hz1 H hH hHz
  have hn1 := hp778 G T (Subgroup.normalizer (L : Set G)) H T h.fsu.simple h.fsu.nonabelian
    h.fsu.qtke h.fsu.sylow ⟨SecA.isMaxTwoLocal_M h331 h, h.normal⟩ hH hlie le_rfl
  have hsylH : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hH.1.1
  rw [sup_comm, SecD.oTwoUpper_sup_eq_of_sylow' hsylH] at hn1
  have hzT : z ∈ T := SecA.fsuV_le_T h hz.1
  have heven : Even (Nat.card H) := by
    rw [even_iff_two_dvd]
    exact dvd_trans (SecD.two_dvd_card_of_ne_bot (hT2.to_le (Subgroup.zpowers_le.mpr hzT))
      (Subgroup.zpowers_ne_bot.mpr hz1))
      (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr (hH.1.1 hzT)))
  exact SecD.nParam_eq_one_of_le_one hn1 heven

theorem stmt11_5_3_ofS (hTwo : SecD.TwoPointsFact) (hCard : SecD.CardVFact)
    (hRank : SecD.RankV2Fact) (hComm : SecD.PointCommFact) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1003 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h1122 : Stmt11_2_2)
    (h1125 : Stmt11_2_5) (h1141 : Stmt11_4_1) (h1142 : Stmt11_4_2) (h1143 : Stmt11_4_3)
    (hp778 : SecB.AS_p778_nParamS) (h44S : Stmt11_4_4S) (h1151 : Stmt11_5_1) : Stmt11_5_3 :=
  SecD.stmt11_5_3_of hTwo hCard hRank hComm h331 h1102 h1003 h1110 h1122 h1125 h1141 h1142 h1143
    (stmt11_4_4_of_p778S hp778 h331 h44S) h1151

end CFSG.Quasithin.Vol2.Ch11.SecE

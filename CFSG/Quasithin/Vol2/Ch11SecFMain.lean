module

public import CFSG.Quasithin.Vol2.Ch11SecFCase1
public import CFSG.Quasithin.Vol2.Ch11SecFKL1b
public import CFSG.Quasithin.Vol2.Ch11SecD557Cases

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

theorem stmt11_5_7Sp4_of (hF : Sp4Facts) (hVL1 : FactSp4VL1) (hV3R1 : FactSp4V3R1)
    (hZC : FactSp4ZCent) (hOpp : FactSp4Opp) (hTr : FactSp4Trans) (hGen : FactSp4Gen)
    (hRL : FactSp4RL) (hF15 : SecA.Facts15) (hN : SecA.NatFacts)
    (h13 : ASInputs.AS_I_1_3_Sp4) (h132 : ASInputs.AS_C_1_32) (hCX : Obl11_5_7Sp4CX)
    (hAl : Obl11_5_7Sp4Alpha) (hY : Obl11_5_7Sp4Y) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h1113 : Stmt11_1_3) (h1114 : Stmt11_1_4)
    (h1115 : Stmt11_1_5) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1155 : Stmt11_5_5) (h1156 : Stmt11_5_6) : SecD.Stmt11_5_7Sp4 := by
  intro G _ _ T L I n V₁ h hV₁ hk
  by_contra hW
  obtain ⟨-, V₂, V₃, -, hV₂, hV₃, -, -, -, -, -⟩ := SecA.exists_isVi hN h1102 h
  have hV₁₃ : V₁ ≤ V₃ := SecA.IsVi.mono₁₃ hN h1102 h hV₁ hV₃
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  have hO : pCoreOf 2 L = fsuV T I := by
    by_cases hR : Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)
    · exact pCoreOf_eq_fsuV_of_le hF hV3R1 hOpp hTr hGen hRL hF15 hN h13 h132 hCX hAl h331
        h1102 h1103 h1110 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk hV₁₃ hW hR
    · exact pCoreOf_eq_fsuV_of_not_le hF h13 h1102 h1115 h hset hk hV₁ hV₂ hR
  by_cases hK : KOf L V₁ V₁ = LOf L V₁
  · exact false_of_kOf_eq_of_pCoreOf_eq hF hVL1 h1102 h1103 h1113 h1114 h1141 h1143 h1154 h1155
      h1156 h hV₁ hV₂ hV₃ hk hK hO hV₁₃
  · exact false_of_kOf_ne hF hZC hVL1 hY h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂
      hV₃ hk hW hK hO

end CFSG.Quasithin.Vol2.Ch11.SecF

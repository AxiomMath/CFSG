module

public import CFSG.Quasithin.Vol2.Ch11SecD557H
public import CFSG.Quasithin.Vol2.Ch11SecD557I
public import CFSG.Quasithin.Vol2.Ch11SecD557Cases
public import CFSG.Quasithin.Vol2.Ch11SecDObl557

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem stmt11_5_7SL3_of (hObl : Obl11_5_7SL3End) (hG2 : SecA.FactG2DerivedOrder)
    (hTor : TorusFixSL3Fact) (hComm : CommLOneSL3Fact) (hNat : NatV3Fact) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4)
    (h1155 : Stmt11_5_5) (h1156 : Stmt11_5_6) : Stmt11_5_7SL3 := by
  intro G _ _ T L I n V₁ h hV₁ hSL3
  by_contra hU
  have hyp := almostSpecialL3Hyp_of_kindSL3 hG2 hNat h1102 h1110 h1141 h hV₁ hSL3 hU
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  obtain ⟨x, hx, y, hy, hV, hxy⟩ := exists_weyl D hyp.base.le_V
  have hS := pCoreOf_le_S₂ hyp hTor hComm h1102 h1110 h1141 h1143 h1154 h1155 h1156 h hV₁ hSL3
    hx hy hV
  rw [S₂_tripleU] at hS
  exact hObl G T L I n V₁ x y h hV₁ hSL3 hU hx hy hV hxy hS

end CFSG.Quasithin.Vol2.Ch11.SecD

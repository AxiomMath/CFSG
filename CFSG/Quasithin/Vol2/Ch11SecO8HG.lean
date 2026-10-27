module

public import CFSG.Quasithin.Vol2.Ch11SecO8HF
public import CFSG.Quasithin.Vol2.Ch11SecDGap556Three

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

theorem gap11_5_6Three_of (hT : FactCCompTorus) (h121 : QuasithinUnique.Id2519.Prop121Three)
    (hT44 : SecE.Facts44) (hCart : CartanFact) (hC : SecS.CartanFacts) (hF : SecA.NatFacts)
    (hTI : PointsTIFact) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1151 : Stmt11_5_1) :
    Gap11_5_6Three := by
  intro G _ _ T L I n V₁ X H₁ h hV₁ hX _ _ _ I' hI' hq
  exact O8H.commutator_le_of_quasisimple hT h121 hT44 hCart hC hF hTI h331 h1102 h1103 h1110
    h1141 h1143 h1151 h hV₁ hX hI' hq

end CFSG.Quasithin.Vol2.Ch11.SecD

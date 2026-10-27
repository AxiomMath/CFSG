module

public import CFSG.Quasithin.Vol2.Ch11SecBG2Main
public import CFSG.Quasithin.Vol2.Ch11SecBDerived22Rad
public import CFSG.Quasithin.Vol2.Ch11SecBDerived22

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

theorem derivedG2WeakClosure_of_parts (hRad : DerivedG2WeakClosureRad) (hFG : FactsG2W)
    (hNF : NatFacts) (hFM : FactMParam) (hFO : FactOddCodim) (hFH : FactHyperplaneT)
    (hS44 : FactSp4FourExt) (hN : FactNot4213) (hFR : FactRootInv)
    (hG2o : FactG2DerivedOrder) (h4213 : TmpL6_4_2_13) (h311 : Theorem311Stmt)
    (h63 : ASInputs.AS_E_6_3) (h612 : ASInputs.AS_E_6_12) (h664 : ASInputs.AS_E_6_6_four)
    (h614 : ASInputs.AS_E_6_14) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1104 : Stmt11_0_4) (h1113 : Stmt11_1_3) (h1114 : Stmt11_1_4) : DerivedG2WeakClosure := by
  intro G _ _ T L I n hyp hG2 g hAT
  by_cases hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · exact derivedG2WeakClosure_cent hFG hNF hFM hFO hFH hS44 hN hFR hG2o h4213 h311 h63 h612
      h664 h614 h331 h1102 h1103 h1104 h1113 h1114 hyp hG2 hC hAT
  · exact hRad G T L I n hyp hG2 hC g hAT

end CFSG.Quasithin.Vol2.Ch11.SecB

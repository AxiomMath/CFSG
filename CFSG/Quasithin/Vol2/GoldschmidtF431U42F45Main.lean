module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Ln2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Poly2

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.F431.F45

theorem facts45L_u42 :
    u42Setting.Facts45L :=
  facts45L_of_model u42XDatum isGenPolygon_incGraph (by rw [card_nbrs_inl])
    (by rw [card_nbrs_inr]; decide) (pCoreOf 2 (MulAction.stabilizer Y (Sum.inl 0 : Vtx)))
    (pCoreOf 2 (MulAction.stabilizer Y (Sum.inr 0 : Vtx))) rfl rfl modelBase_pt modelBase_ln

end CFSG.Quasithin.H13.F431.U42

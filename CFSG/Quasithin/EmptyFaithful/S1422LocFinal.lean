module

public import CFSG.Quasithin.EmptyFaithful.S1422LocTits
public import CFSG.Quasithin.EmptyFaithful.S1422LocG22p

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

theorem lemma14221Local_of_inputs (hVQ : Stage1426VleQ) (hTits : TitsAmalgamLocal)
    (h2F4 : TwoF4AmalgamLocal) (hG2 : G2AmalgamE8) (hM12 : M12AmalgamE8)
    (hAut : AutM12AmalgamLocal) : Lemma14221Local where
  tits G _ _ T _ Y H S hC :=
    Setting1422.titsLike_local card_Sz_zero S hC.2.1 (hTits G H (Y ⊔ T) hC)
  twoF4 G _ _ T _ Y H S hC :=
    Setting1422.titsLike_local card_Sz_zero S (Or.inr hC.2.1) (h2F4 G H (Y ⊔ T) hC)
  g2 _ _ _ _ _ _ _ S hC := Setting1422.g2_local hVQ hG2 S hC
  g22p _ _ _ _ _ _ _ S hC := Setting1422.g22p_local S hC
  m12 _ _ _ _ _ _ _ S hC := Setting1422.m12_local hVQ hM12 S hC
  autM12 _ _ _ _ _ _ _ S hC := Setting1422.autM12_local hVQ hAut S hC

end CFSG.Quasithin

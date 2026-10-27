module

public import CFSG.Quasithin.EmptyFaithful.A38cBasic
public import CFSG.Quasithin.EmptyFaithful.S153F21
public import CFSG.Quasithin.EmptyFaithful.A38cOrders

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.H13.VolI

theorem a7NotA38Type_holds :
    A7NotA38Type := by
  intro G _ L ⟨α, hα, hk⟩ hA
  have hc := card_quot_pCore_of_surjective α hα hk
  rw [Vol2.Ch10.SecA.card_alt 7 (by norm_num)] at hc
  have h2520 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2520 := by
    rw [hc]
    decide
  exact not_a38Order_2520 (h2520 ▸ a38Order_card hA)

end CFSG.Quasithin

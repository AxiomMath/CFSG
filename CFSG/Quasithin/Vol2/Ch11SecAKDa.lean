module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Background.S1549DL3N
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint

theorem factG2AdjointOrder_holds : FactG2AdjointOrder := by
  intro K _ _ n _ hK
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointQuotient,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK, ordG2, mul_assoc]

theorem factG2DerivedTwoOrder_holds : FactG2DerivedTwoOrder :=
  fun _ _ _ hK => CFSG.Quasithin.S1549D.card_commutator_quasithinG2_two hK

end CFSG.Quasithin.Vol2.Ch11.SecA

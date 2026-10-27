module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint

theorem fact3D4Order_holds : Fact3D4Order := by
  intro X _ n hn hX
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hn hX.2,
    ordTrialityD4]
  ring

end CFSG.Quasithin.Vol2.Ch11.SecA

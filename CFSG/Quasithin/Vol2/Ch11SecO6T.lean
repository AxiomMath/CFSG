module

public import CFSG.Quasithin.Vol2.Ch11SecO6Q
public import CFSG.Quasithin.Vol2.Ch11SecO6S7

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Quasithin.Vol2.Ch11.O6


theorem factOut2Case1_holds : FactOut2Case1 :=
  factOut2Case1_of_inverts fun _ _ _ hD hX r _ hrF _ hs hs2 _ =>
    inverts_of_perfect r hD hX hrF hs hs2

end CFSG.Quasithin.Vol2.Ch11.SecE

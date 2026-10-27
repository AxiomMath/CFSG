module

public import CFSG.Quasithin.Background.C22PfC
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin

theorem asc22Three_of_a37 (h : A37ForSQTK) (G : Type) [Group G] [Finite G] : ASC22Three G :=
  C22Pf.asc22Three_of h

end CFSG.Quasithin

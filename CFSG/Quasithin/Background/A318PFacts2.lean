module

public import CFSG.Quasithin.Background.A318PAut
public import CFSG.Quasithin.Background.A318PC14
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.Quasithin.Background.A318PF4Frame

public section

namespace CFSG.Quasithin

theorem a318Facts_of_two
    (qs : QSporOutTwo) (ql : QLiePRank) : A318Facts :=
  { aut := A318P.a318AutFact_of qs ql A318P.qLieThreeRank_native,
    center := a318CenterFact,
    central := A318P.a318CentralFact_native,
    list := a23SQTKListFact }

end CFSG.Quasithin

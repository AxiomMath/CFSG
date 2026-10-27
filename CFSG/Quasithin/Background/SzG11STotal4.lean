module

public import CFSG.Quasithin.Background.SzG11STotal3
public import CFSG.Quasithin.Background.SzG11B49Main
public import CFSG.Quasithin.Background.SzG11TwoOm4

public section

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

structure G112InputsS4 : Prop where
  g93 : G93StmtDimensionOnly
  g2 : NoConfigG2Two

theorem theoremG112FixS_of_inputs4
    (hA21 : AsA21SQTKSection) (h56 : AsB56) (h : G112InputsS4) : TheoremG112FixS :=
  theoremG112FixS_of_inputs3 hA21 h56 ⟨h.g93, b49, noConfigOm4MinusTwo, h.g2⟩

end SzG11S

end G11

end CFSG.Quasithin

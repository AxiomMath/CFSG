module

public import CFSG.Quasithin.Background.SzG11STotal2
public import CFSG.Quasithin.Background.SzG11M12Main
public import CFSG.Quasithin.Background.SzG11TwoSp4

public section

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

structure G112InputsS3 : Prop where
  g93 : G93StmtDimensionOnly
  b49 : B49Stmt
  om4Minus : NoConfigOm4MinusTwo
  g2 : NoConfigG2Two

theorem theoremG112FixS_of_inputs3
    (hA21 : AsA21SQTKSection) (h56 : AsB56) (h : G112InputsS3) : TheoremG112FixS :=
  theoremG112FixS_of_inputs2 hA21 h56
    ⟨h.g93, h.b49, noConfigM12, h.om4Minus, noConfigSp4Two, h.g2⟩

end SzG11S

end G11

end CFSG.Quasithin

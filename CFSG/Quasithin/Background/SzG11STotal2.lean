module

public import CFSG.Quasithin.Background.SzG11STotal
public import CFSG.Quasithin.Background.SzG11B5b2
public import CFSG.Quasithin.Background.SzG11B5c
public import CFSG.Quasithin.Background.SzG11TensorMain

public section

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

structure G112InputsS2 : Prop where
  g93 : G93StmtDimensionOnly
  b49 : B49Stmt
  m12 : NoConfigM12
  om4Minus : NoConfigOm4MinusTwo
  sp4 : NoConfigSp4Two
  g2 : NoConfigG2Two

theorem theoremG112FixS_of_inputs2
    (hA21 : AsA21SQTKSection) (h56 : AsB56) (h : G112InputsS2) : TheoremG112FixS :=
  theoremG112FixS_of_inputs hA21 h56
    ⟨h.g93, g115b_of_parts g115bPart1 (g115bPart2_of_asA21 hA21), h.b49, h.m12, h.om4Minus,
      h.sp4, h.g2, om4PlusTensor⟩

end SzG11S

end G11

end CFSG.Quasithin

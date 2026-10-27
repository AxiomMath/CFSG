module

public import CFSG.Quasithin.Background.SzG11STotal5
public import CFSG.Quasithin.EmptyFaithful.SzPS8FromInputs

public section

namespace CFSG.Quasithin

namespace SzPS8

theorem theoremG112FixS_of_g93
    (hA21 : AsA21SQTKSection) (h56 : AsB56) (g93 : G11.G93StmtDimensionOnly) :
    TheoremG112FixS :=
  theoremG112FixS_of_szG11S (G11.SzG11S.theoremG112FixS_of_g93 hA21 h56 g93)

theorem theoremG112Fix_of_g93
    (hA21 : AsA21SQTKSection) (h56 : AsB56) (g93 : G11.G93StmtDimensionOnly) :
    G11.TheoremG112Fix :=
  theoremG112Fix_of_S (theoremG112FixS_of_g93 hA21 h56 g93)

end SzPS8

end CFSG.Quasithin

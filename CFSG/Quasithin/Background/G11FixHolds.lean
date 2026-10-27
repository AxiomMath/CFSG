module

public import CFSG.Quasithin.EmptyFaithful.SzPS8FromG93
public import CFSG.Quasithin.Background.Harris.HoldsDimensionOnly
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51

public section

namespace CFSG.Quasithin

theorem G11.theoremG112Fix_holds :
    G11.TheoremG112Fix :=
  SzPS8.theoremG112Fix_of_g93 asA21SQTKSection asB56_holds
    G11.Harris.g93StmtDimensionOnly_holds

theorem G11.SzG11S.theoremG112FixS_holds :
    G11.SzG11S.TheoremG112FixS :=
  G11.SzG11S.theoremG112FixS_of_g93 asA21SQTKSection asB56_holds
    G11.Harris.g93StmtDimensionOnly_holds

end CFSG.Quasithin

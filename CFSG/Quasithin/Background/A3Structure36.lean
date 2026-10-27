
module


public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36B

public section

namespace CFSG.Quasithin

theorem a36 (hF : A36Facts) {G : Type} [Group G] (hG : SQTKHyp G) : A36Statement G :=
  a36_of_caseB hF (a36_caseB hF.toA36CaseBFacts) hG

end CFSG.Quasithin

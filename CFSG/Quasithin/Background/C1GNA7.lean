
module

public import CFSG.Quasithin.Background.C1GNA7Base

public import CFSG.Quasithin.Background.A3Structure36
public import CFSG.Quasithin.Background.A3Structure37
public import CFSG.Quasithin.Background.A3Structure38Part3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.SectionRank

namespace C1GN

section Normality

variable {G : Type} [Group G] [Finite G]

theorem a38Part3_quotient (hF36 : A36Facts) (hF38 : A38Facts) {X : Subgroup G}
    (hSQ : IsSQTKTC X) : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X) := by
  have hG := SQTKHyp.of_sqtkGroup (↥X) (isSQTKTC_iff_sqtkGroup.1 hSQ)
  have h36 := a36 hF36 hG
  exact A38.a38_part3 hF38 hG h36 (A37.a37_of_a36 h36)

end Normality

end C1GN

end CFSG.Quasithin

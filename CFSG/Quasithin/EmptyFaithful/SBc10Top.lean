module

public import CFSG.Quasithin.EmptyFaithful.SBc9Top
public import CFSG.Quasithin.EmptyFaithful.SBc10G2Block

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc10


theorem input31G2NoFixed_holds (h113 : StageLemma14113) : Input31G2NoFixed := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c _ hG
  exact (g2_facts h113 c.toCtx15330 hG).1

theorem input31G2Cover_holds (h113 : StageLemma14113) : Input31G2Cover := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c _ hG
  exact (g2_facts h113 c.toCtx15330 hG).2

theorem input15331_of_msOutcome (h113 : StageLemma14113) (hMS : Input31MSOutcome) : Input15331 :=
  SBc9.input15331_of_g2_module_facts h113 hMS (input31G2NoFixed_holds h113)
    (input31G2Cover_holds h113)

end SBc10

end CFSG.Quasithin

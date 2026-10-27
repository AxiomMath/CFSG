module

public import CFSG.Quasithin.EmptyFaithful.SzN17Ctx
public import CFSG.Quasithin.EmptyFaithful.SBc4C26

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem input26ComponentBase_of_a3 (h56 : AsB56) (h39 : A39ForSQTK) : Input26ComponentBase := by
  intro G _ _ T Mc M V₁ V₂ Yp I t c hF
  obtain ⟨L, hL, hLn, hL3, hq, -⟩ :=
    SzN17.exists_cComp_not_le h56 h39 c.hyp c.inH c.charTwo hF.toFacts153
  exact ⟨L, hL, hLn, hL3, hq⟩

end CFSG.Quasithin

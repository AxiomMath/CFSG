module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveRank
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveL32
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationElevenH
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTenGlobal

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem false_of_through
    [Finite G] (hfact : L32AutFact) (hQ : quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) (h139 : E.Through139)
    (h1310 : E.Through1310) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htK, -, -⟩ := h139
  obtain ⟨ℓ, c, hF, -, hc3, -, -, hcs, hEc, hEW⟩ := h1310
  have hℓ : ℓ = false := E.frame_eq_false hT hM hF hcs hEc htK
  subst hℓ
  rcases E.H_iso hQ.2.1 hT hM hcs hc3 hEc hEW with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact E.false_of_L32 hfact hcs hc3 hEc hEW e
  · exact E.false_of_alternating_six hQ
      (E.x₃_centralizes_HH hQ.2.1 hT hM hcs hc3 hEc hEW e) e

end Emb

end CFSG.Quasithin.A10

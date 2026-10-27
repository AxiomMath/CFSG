module

public import CFSG.Quasithin.Background.C48SporCoverHS

public section

namespace CFSG.Quasithin.C48Cover

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def C48SporCoverM22 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → CFSG.Open.IsComponentOf K H →
    C31Conclusion H R M L V K → C31Case3 H R M L V K → IsPSL 3 2 1 (ModO2 L) →
      V ⊓ centerOf K = ⊥

@[expose] def C48SporCoverRu (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → CFSG.Open.IsComponentOf K H →
    C31Conclusion H R M L V K → C31Case9 H R M L V K → IsPSL 3 2 1 (ModO2 L) →
      V ⊓ centerOf K = ⊥

theorem c48SporCoverFact_of
    {G : Type} [Group G] [Finite G] (hM22 : C48SporCoverM22 G) (hRu : C48SporCoverRu G) :
    C48SporCoverFact G := by
  intro H R M L V K h hK hc hcase hpsl
  rcases hcase with h3 | h7 | h9
  · exact hM22 H R M L V K h hK hc h3 hpsl
  · exact c48SporCoverHS_holds H R M L V K h hK hc h7 hpsl
  · exact hRu H R M L V K h hK hc h9 hpsl

end CFSG.Quasithin.C48Cover

module

public import CFSG.Quasithin.Background.C3Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def C48SporCoverFact (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → CFSG.Open.IsComponentOf K H →
    C31Conclusion H R M L V K →
    (C31Case3 H R M L V K ∨ C31Case7 H R M L V K ∨ C31Case9 H R M L V K) →
    IsPSL 3 2 1 (ModO2 L) → V ⊓ centerOf K = ⊥

end CFSG.Quasithin

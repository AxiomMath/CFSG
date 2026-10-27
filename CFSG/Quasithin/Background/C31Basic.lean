module

public import CFSG.Quasithin.Background.C3Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

@[expose] def C31Basic (_H _R M L _V K : Subgroup G) : Prop :=
  conjClosure L M ≤ K ∧ M ≤ Subgroup.normalizer (K : Set G) ∧ IsPGroup 2 ↥(centerOf K)

theorem C31Conclusion.basic {H R M L V K : Subgroup G} (h : C31Conclusion H R M L V K) :
    C31Basic H R M L V K :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

end CFSG.Quasithin

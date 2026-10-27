module

public import CFSG.Quasithin.EmptyFaithful.S152ObsF7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

abbrev nOfR152 (T Mc M : Subgroup G) : Subgroup G :=
  M ⊓ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)

theorem stageObserveF7N_of (h1519 : StageLemma1519) :
    ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
      ∀ H : Subgroup G, IsHStar T M H →
        AmalgamHypV (nOfR152 T Mc M ⊔ H) (nOfR152 T Mc M) H T (V154 T Mc M) :=
  fun G _ _ T Mc M hs _ hH =>
    amalgamHypV_normalizer hs hH (h1519 G T Mc M hs.qtfe hs.mf hs.ce)

end CFSG.Quasithin

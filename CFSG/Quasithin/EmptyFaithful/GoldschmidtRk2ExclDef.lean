module

public import CFSG.Quasithin.EmptyFaithful.S151S2

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def Input15120RankTwoNoSwap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ListB15120' L →
    s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) →
    ∀ P : Subgroup G, IsMaxParabolic2 L P →
      L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤ P →
      s1516 T Z₁ ≤ Subgroup.normalizer (P : Set G)

end CFSG.Quasithin.Rk2

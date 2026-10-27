module

public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def Conf4212NoSumBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G),
    Hyp4_2_3 G T M L Mm I → InM I H → Conf4212 G T M L I H K →
    ∀ m k : ℕ, (m = 3 ∨ m = 4) → m ≤ k → k ≤ 4 →
      IsPSL m 2 1 (ModO2 (perfectCore (L ⊓ H))) →
      IsSumOfNaturalModules (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆ ⊥
        ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I))
        (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k → False

end CFSG.Quasithin.H13.Ch4

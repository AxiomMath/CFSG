module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def C48SumBound (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (H R M L V : Subgroup G) (m k : ℕ), HypC28 H R M L V → M < H → ¬ oTwoFstarIn H ≤ M →
    (m = 3 ∨ m = 4) →
    IsPSL m 2 1 (ModO2 L) →
    IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) (StatedSL m (ZMod 2)) false k →
    k ≤ 4

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.B610
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def B610Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V L : Subgroup G) (n : ℕ),
    MinParabolic H T M → CharTwo H → IsTwoReducedIn H V → L ≤ H →
    H ≤ Subgroup.normalizer (L : Set G) → H = L ⊔ T →
    (∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal →
      (∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = L) →
    L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L → 2 ≤ n →
    IsNaturalL2Prime n L V → ⁅V, thompsonJ T⁆ ≠ ⊥ →
      IsSylowTwoOf (baum T) (baum T ⊔ L)

end CFSG.Quasithin

end

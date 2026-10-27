module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Pointwise

@[expose] def AsC135Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R₀ L : Subgroup G) (n : ℕ) (F : Type) [Field F]
    [Fintype F] (α : ↥L →* ↥(StatedSL 3 F)),
    IsMSPair G₀ R₀ → L ∈ cComp G₀ → (G₀ : Set G) = (L : Set G) * (R₀ : Set G) →
    G₀ ≤ Subgroup.normalizer (L : Set G) → 2 ≤ n →
    Fintype.card F = 2 ^ n → IsModO2Surj L α →
    G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    IsSumOfNaturalModulesVia L (centerOf (c134Q G₀ L)) ⊥ α false 1 →
    IsSumOfNaturalModulesVia L (c134Q G₀ L) (centerOf (c134Q G₀ L)) α true 2 →
      pCoreOf 2 G₀ = c134Q G₀ L

end CFSG.Quasithin.H13.Ch4

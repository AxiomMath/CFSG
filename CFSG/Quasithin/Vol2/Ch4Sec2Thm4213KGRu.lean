module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def KGG2BlockRuFF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K B W : Subgroup G),
    ⁅K, K⁆ = K → IsSporadic .Ru (↥K ⧸ Subgroup.center ↥K) → B ≤ K →
      CFSG.Quasithin.IsG2Block B → W ≤ blockU B → W ⊓ blockZ B = ⊥ →
      B ≤ Subgroup.normalizer (W : Set G) → Nat.card W = 2 ^ 6 →
        ∃ _ : IsMulCommutative ↥W,
          IsFFModule (V := ↥W) (autOn (K ⊓ Subgroup.normalizer (W : Set G)) W)

end CFSG.Quasithin.H13.Ch4

module

public import CFSG.Quasithin.Background.F918Z8Def3
public import CFSG.Quasithin.Background.F918V3Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def SuzFFClass : Prop :=
  ∀ (Y : Type) [CommGroup Y] [Finite Y] (Γ Λ S : Subgroup (MulAut Y)) (V : Subgroup Y),
    LocCfg Γ Λ S V → (∃ n, IsSz n ↥Λ) → ∀ A ∈ QhatStar Γ, A ≤ S →
      (∀ a ∈ A, ∀ x ∈ Λ, a * x = x * a) →
      ∀ X : Subgroup (MulAut Y), X ≤ Γ → (∀ x ∈ X, ∀ y ∈ Λ, x * y = y * x) →
        A ≤ Subgroup.normalizer (X : Set (MulAut Y)) → ⁅X, A⁆ = X → X ≠ ⊥ →
        (∃ K : Subgroup (MulAut Y), IsComponentOf K Γ ∧ ¬ IsSuzukiComponent K ∧
          X = ⨆ a ∈ A, conjAutSub a K) → 3 ∣ Nat.card ↥X →
        ∀ W : Subgroup Y, W ≠ ⊥ → (∀ l ∈ Λ, ∀ w ∈ W, l w ∈ W) → A ≤ stabSub W →
          X ≤ stabSub W → (∀ b ∈ A, (∀ x ∈ X, b * x = x * b) → ∀ w ∈ W, b w = w) →
          (∃ x ∈ X, ∃ w ∈ W, x w ≠ w) → commSub W A ≠ ⊥ →
          IsA2 (autSub Γ W) (autSub A W) → commSeries (autSub A W) 3 = ⊥ →
          rAV (autSub A W) ≤ 2 →
          5 ∣ Nat.card ↥X ∨ ∃ m : ℕ, 1 ≤ m ∧
            Nat.card ↥Λ ∣ ∏ i : Fin 4, ((2 ^ m) ^ 4 - (2 ^ m) ^ (i : ℕ)) ∧
            ∀ p : ℕ, p.Prime → p ∣ ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) → p ∣ Nat.card ↥X

end CFSG.Quasithin

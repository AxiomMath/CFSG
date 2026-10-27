module

public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def IsSuzukiComponent {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∃ e : ℕ, IsSz e (↥K ⧸ Subgroup.center ↥K)

@[expose] def D392 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → Mp = L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
    (V = orbSup T V ∨ (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L)) →
    ∀ A : Subgroup (MulAut W), A ∈ QhatStar M → A ≤ T →
      (∃ a ∈ A, a ≠ 1 ∧ ∀ x ∈ Mp, a * x = x * a) →
      ∃ X : Subgroup (MulAut W), X ≠ ⊥ ∧ X ≤ M ∧ (∀ x ∈ X, ∀ y ∈ Mp, x * y = y * x) ∧
        A ≤ Subgroup.normalizer (X : Set (MulAut W)) ∧
        ⁅X, A ⊓ Subgroup.centralizer (Mp : Set (MulAut W))⁆ = X ∧
        ((∃ K : Subgroup (MulAut W), IsComponentOf K M ∧ ¬ IsSuzukiComponent K ∧
            X = ⨆ a ∈ A, conjAutSub a K) ∨
          (X ≤ pCoreOf 3 M ∧ Nat.card ↥X = 3)) ∧
        (∀ q : ℕ, q.Prime → q ≠ 3 → ∀ a ∈ A, ∀ x ∈ pCoreOf q M, a * x = x * a) ∧
        (∀ K : Subgroup (MulAut W), IsComponentOf K M → IsSuzukiComponent K →
          (∀ x ∈ K, ∀ y ∈ Mp, x * y = y * x) → ∀ a ∈ A, ∀ x ∈ K, a * x = x * a) ∧
        3 ∣ Nat.card ↥X

@[expose] def D392Suzuki : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → Mp = L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
    (V = orbSup T V ∨ (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L)) →
    ∀ A : Subgroup (MulAut W), A ∈ QhatStar M → A ≤ T →
      (∃ a ∈ A, a ≠ 1 ∧ ∀ x ∈ Mp, a * x = x * a) →
      ∀ K : Subgroup (MulAut W), IsComponentOf K M → IsSuzukiComponent K →
        (∀ x ∈ K, ∀ y ∈ Mp, x * y = y * x) → ∀ a ∈ A, ∀ x ∈ K, a * x = x * a

end CFSG.Quasithin

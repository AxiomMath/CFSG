module

public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D321OpCore : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D3Std M Mp T L V → t ∈ T → t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
    Mp = L ⊔ conjAutSub t L → ∀ g ∈ M, (∀ x ∈ L, g * x = x * g) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥L → (∃ k : ℕ, g ^ (p ^ k) = 1) →
    g ∈ conjAutSub t L

@[expose] def InvSylAll {G : Type*} [Group G] (L : Subgroup G) (p : ℕ) : Prop :=
  ∀ P : Subgroup G, P ≤ L → IsPGroup p P → (∃ m : ℕ, Nat.card L = Nat.card P * m ∧ ¬ p ∣ m) →
    ∃ τ ∈ L, τ * τ = 1 ∧ ∀ x ∈ P, τ * x * τ⁻¹ = x⁻¹

@[expose] def ExcPair (X : Type) [Group X] (p : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ 3 < q ∧ q % 4 = 3 ∧ p = q ∧ IsPSL 2 q 1 X


@[expose] def D321OpExc : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D3Std M Mp T L V → t ∈ T → t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
    Mp = L ⊔ conjAutSub t L → ∀ g ∈ M, (∀ x ∈ L, g * x = x * g) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥L → (∃ k : ℕ, g ^ (p ^ k) = 1) →
    ExcPair ↥L p → g ∈ conjAutSub t L

end CFSG.Quasithin

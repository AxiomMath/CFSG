module

public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

structure LocCfg {Y : Type} [CommGroup Y] [Finite Y] (Γ Λ S : Subgroup (MulAut Y))
    (V : Subgroup Y) : Prop where
  std : D3Std Γ Λ S Λ V
  hq : qhatOf Γ ≤ ((2 : ℚ) : WithTop ℚ)
  VS : V = orbSup S V
  ne : V ≠ ⊤
  fix : fixV Λ = ⊥
  a38 : A38Types ↥Λ
  hK : ∀ g ∈ Γ, (∀ x ∈ Λ, g * x = x * g) → ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥Λ →
    (∃ k : ℕ, g ^ (p ^ k) = 1) → g = 1

@[expose] def LocShape {Y : Type} [CommGroup Y] (Λ : Subgroup (MulAut Y)) : Prop :=
  (IsPSL 3 2 1 ↥Λ ∧ DirectSumOfCopies Λ ⊤ ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4) ∨
  ∃ n, IsPSL 2 2 n ↥Λ ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    DirectSumOfCopies Λ ⊤ ⊥ (FFModel.nat (StatedSL 2 K)) 2

@[expose] def D321Local : Prop :=
  ∀ (Y : Type) [CommGroup Y] [Finite Y] (Γ Λ S : Subgroup (MulAut Y)) (V : Subgroup Y),
    LocCfg Γ Λ S V → LocShape Λ

@[expose] def D321OpPrimeC : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D3Std M Mp T L V → t ∈ T → t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
    Mp = L ⊔ conjAutSub t L → (∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) →
    ∀ g ∈ M, (∀ x ∈ L, g * x = x * g) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥L → (∃ k : ℕ, g ^ (p ^ k) = 1) →
    ∀ u ∈ commV L, g u = u

@[expose] def D321Exact : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W) (A : Subgroup (MulAut W)),
    D3Std M Mp T L V → t ∈ T → t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
    Mp = L ⊔ conjAutSub t L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) → QOff Mp T A (orbSup T V) →
    (∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) → V < orbSup T V → commSub (orbSup T V) L = V →
    qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) → orbSup T V ≠ ⊤ →
    IsPSL 3 2 1 ↥L →
    DirectSumOfCopies L (commV L) (commV L ⊓ fixV Mp) (FFModel.nat (StatedSL 3 (ZMod 2))) 4 →
    commV L ⊓ fixV Mp = ⊥

end CFSG.Quasithin

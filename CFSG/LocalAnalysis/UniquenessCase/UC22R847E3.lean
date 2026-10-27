module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def R847E3Thin (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, (Y.subgroupOf D.M).Normal → F08.Thin8 Y → ∀ X : Subgroup G, X ≤ Y →
    ∀ q : ℕ, q.Prime → q ≠ 2 → Nat.card X = q → ∀ p ∈ D.sig,
      normalizer (X : Set G) ≤ D.M ∨
        (p = 3 ∧ 2 ≤ CFSG.Open.pRank 3 (barPreimage D.M (centE D.M)))

@[expose] def R847E3SU3 (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, (Y.subgroupOf D.M).Normal → ∀ n : ℕ, IsSU3 (Bar2 Y) n →
    ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 2 ^ n - 1 → Nat.card X = q →
      ∀ p ∈ D.sig, normalizer (X : Set G) ≤ D.M ∨ (p = 3 ∧ Odd n)

@[expose] def R847E3Dvd (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, (Y.subgroupOf D.M).Normal → ∀ n : ℕ, IsSU3 (Bar2 Y) n →
    ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 2 ^ n - 1 → Nat.card X = q →
      ∀ p ∈ D.sig, 5 ≤ p → p ∣ 2 ^ n + 1 → normalizer (X : Set G) ≤ D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22

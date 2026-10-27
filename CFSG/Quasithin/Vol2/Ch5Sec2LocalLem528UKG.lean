module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def FactU4ParabolicModule : Prop :=
  ∀ (Y : Type) [Group Y] (m : ℕ) (T M₁ M : Subgroup Y), 2 ≤ m →
    (IsLieOverTwo .PSU 4 m Y ∨
      ∃ (Y₀ : Type) (_ : Group Y₀) (ι : Y₀ →* Y), IsLieOverTwo .PSU 4 m Y₀ ∧
        Function.Injective ι ∧ ι.range.index = 2) →
    IsYAmalgamPair T M₁ M → IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (perfectCore M)) →
      perfectCore M ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore M)) : Set Y) ∧
        ⁅pCoreOf 2 (perfectCore M), perfectCore M⁆ = pCoreOf 2 (perfectCore M) ∧
        ∀ R : Subgroup Y, R ≤ pCoreOf 2 (perfectCore M) →
          perfectCore M ≤ Subgroup.normalizer (R : Set Y) →
          ¬ R ≤ centerOf (pCoreOf 2 (perfectCore M)) →
          R ⊔ centerOf (pCoreOf 2 (perfectCore M)) ≠ pCoreOf 2 (perfectCore M) →
            ⁅R, pCoreOf 2 (perfectCore M)⁆ = centerOf (pCoreOf 2 (perfectCore M)) ∧
              Nat.card ↥(R ⊔ centerOf (pCoreOf 2 (perfectCore M))) = (2 ^ m) ^ 3

@[expose] def FactU4ExtCenter : Prop :=
  ∀ (Y : Type) [Group Y] (m : ℕ) (T M₁ M : Subgroup Y), 2 ≤ m →
    (∃ (Y₀ : Type) (_ : Group Y₀) (ι : Y₀ →* Y), IsLieOverTwo .PSU 4 m Y₀ ∧
        Function.Injective ι ∧ ι.range.index = 2) →
    IsYAmalgamPair T M₁ M → IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (perfectCore M)) →
      ∀ t ∈ M, t ^ 2 = 1 → t ∉ pCoreOf 2 (perfectCore M) →
        (∀ k ∈ perfectCore M, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore M)) →
          t ∈ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore M)) : Set Y)

end CFSG.Quasithin.H13

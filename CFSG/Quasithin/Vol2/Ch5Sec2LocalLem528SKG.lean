module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def FactG2D4ParabolicIrred : Prop :=
  ∀ (Y : Type) [Group Y] (n : ℕ) (T M₁ M : Subgroup Y),
    ((3 ≤ n ∧ IsLieOverTwo .G2 0 n Y ∧ IsSpecialPow 2 (2 ^ n) 2 ↥(pCoreOf 2 (perfectCore M))) ∨
      (1 ≤ n ∧ IsLieOverTwo .trialityD4 0 n Y ∧
        IsSpecialPow 2 (2 ^ n) 4 ↥(pCoreOf 2 (perfectCore M)))) →
    IsYAmalgamPair T M₁ M →
      perfectCore M ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore M)) : Set Y) ∧
        ∀ W : Subgroup Y, centerOf (pCoreOf 2 (perfectCore M)) ≤ W →
          W ≤ pCoreOf 2 (perfectCore M) → perfectCore M ≤ Subgroup.normalizer (W : Set Y) →
            W = centerOf (pCoreOf 2 (perfectCore M)) ∨ W = pCoreOf 2 (perfectCore M)

@[expose] def FactG24ParabolicCenter : Prop :=
  ∀ (Y : Type) [Group Y] (T M₁ M : Subgroup Y), IsLieOverTwo .G2 0 2 Y →
    IsYAmalgamPair T M₁ M → IsSpecialPow 2 4 2 ↥(pCoreOf 2 (perfectCore M)) →
      perfectCore M ≤ Subgroup.centralizer (centerOf (pCoreOf 2 (perfectCore M)) : Set Y) ∧
        ∀ R : Subgroup Y, R ≤ pCoreOf 2 (perfectCore M) →
          perfectCore M ≤ Subgroup.normalizer (R : Set Y) →
          ¬ R ≤ centerOf (pCoreOf 2 (perfectCore M)) →
            centerOf R ≤ centerOf (pCoreOf 2 (perfectCore M))

@[expose] def FactX3ParabolicG2 : Prop :=
  ∀ (Y : Type) [Group Y] (T M₁ M : Subgroup Y), IsLieOverTwo .G2 0 2 Y →
    IsYAmalgamPair T M₁ M → IsSpecialPow 2 4 2 ↥(pCoreOf 2 (perfectCore M)) →
      ∃ x ∈ M, orderOf x = 3 ∧
        ∀ k ∈ perfectCore M, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore M)

@[expose] def FactX3ParabolicU4 : Prop :=
  ∀ (Y : Type) [Group Y] (T M₁ M : Subgroup Y),
    (IsLieOverTwo .PSU 4 2 Y ∨
      ∃ (Y₀ : Type) (_ : Group Y₀) (ι : Y₀ →* Y), IsLieOverTwo .PSU 4 2 Y₀ ∧
        Function.Injective ι ∧ ι.range.index = 2) →
    IsYAmalgamPair T M₁ M → IsSpecialPow 2 4 2 ↥(pCoreOf 2 (perfectCore M)) →
      ∃ x ∈ M, orderOf x = 3 ∧
        ∀ k ∈ perfectCore M, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore M)

@[expose] def AutA7Fact : Prop :=
  ∀ φ : MulAut (alternatingGroup (Fin 7)), φ ^ 3 = 1 →
    ∀ H : Subgroup (alternatingGroup (Fin 7)), Nat.card H = 60 →
      (∀ h ∈ H, φ h = h) → φ = 1

@[expose] def FactExcParabolicO2NeSq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G) (m : ℕ), 2 ≤ m →
    ((∃ f : ℕ, (2 ≤ f ∧ IsG2 2 f ↥L) ∨ (1 ≤ f ∧ Is3D4 2 f ↥L) ∨
        (Odd f ∧ 3 ≤ f ∧ Is2F4 f ↥L)) ∨ IsTits ↥L) →
    IsMaxParabolic2 L P → IsPSL 2 2 m (ModO2 (perfectCore P)) →
      Nat.card (CFSG.pCore 2 ↥(perfectCore P)) ≠ (2 ^ m) ^ 2

end CFSG.Quasithin.H13

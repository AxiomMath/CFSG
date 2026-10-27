module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def InputSchurSL2 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ k →
    ∀ (X : Type) [Group X] [Finite X] (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F),
      Function.Surjective φ → commutator X = ⊤ → CFSG.pCore 2 X = ⊥ →
        φ.ker ≤ Subgroup.center X → Function.Injective φ

@[expose] def DerivedL2List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G) (k : ℕ),
    Hyp11 G T L I n → IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ → E1.nParam H = k → 2 ≤ k →
    K ∈ cComp H → H = K ⊔ T → CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) →
    E2.E22Cases H T (H ⊓ Subgroup.normalizer (L : Set G)) K →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
        ∃ φ : ↥K ⧸ CFSG.pCore 2 ↥K →* Matrix.SpecialLinearGroup (Fin 2) F,
          Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)

@[expose] def DerivedTwoComponents : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K D : Subgroup G) (k p : ℕ),
    Hyp11 G T L I n → IsHStar T (Subgroup.normalizer (L : Set G)) H →
    K ∈ cComp H → H = K ⊔ T → E2.E22Cases H T (H ⊓ Subgroup.normalizer (L : Set G)) K →
    ¬ T ≤ Subgroup.normalizer (K : Set G) → 2 ≤ k → E1.nParam H = k →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G)) →
    (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) →
    T ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (L : Set G)) ⊔ (T ⊓ Subgroup.normalizer (D : Set G)) →
    p.Prime → p ≠ 2 → p ∣ 2 ^ k - 1 →
      ∃ t ∈ T, t ∈ Subgroup.normalizer (D : Set G) ∧
        ∃ d ∈ D, d ^ p = 1 ∧ t * d * t⁻¹ ∉ Subgroup.zpowers d

end CFSG.Quasithin.Vol2.Ch11.SecB

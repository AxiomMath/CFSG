module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def FactSL2SylowNormalizer : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), IsPGroup 2 U → Nat.card U = 2 ^ n →
      Subgroup.normalizer (U : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ≠ ⊤ ∧
        ∃ d ∈ Subgroup.normalizer (U : Set (Matrix.SpecialLinearGroup (Fin 2) F)),
          orderOf d = 2 ^ n - 1

@[expose] def FactBorelOddSL3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ Y U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F), U ≤ Y → IsPGroup 2 U →
      Nat.card U = 2 ^ (3 * n) → (∀ y ∈ Y, Odd (orderOf y) → y ^ (2 ^ n - 1) = 1) →
        Y ≤ Subgroup.normalizer (U : Set _)

@[expose] def FactBorelOddSp4 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ Y U : Subgroup ↥(StatedSp 2 F), U ≤ Y → IsPGroup 2 U → Nat.card U = 2 ^ (4 * n) →
      (∀ y ∈ Y, Odd (orderOf y) → y ^ (2 ^ n - 1) = 1) → Y ≤ Subgroup.normalizer (U : Set _)

end CFSG.Quasithin.Vol2.Ch11.SecC

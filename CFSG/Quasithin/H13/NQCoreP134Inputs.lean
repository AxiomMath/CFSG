module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

structure OddConfig {A : Type} [Group A] (p : ℕ) (L P T : Subgroup A) : Prop where
  hyp : SQTKHypCat A
  normal : L.Normal
  component : CFSG.IsComponent L
  le : P ≤ L
  exp : ∀ x ∈ P, x ^ p = 1
  card : Nat.card P = p ^ 2 ∨ Nat.card P = p ^ 3
  sylow : IsSylowTwoOf T ⊤
  mul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s
  irred : ∀ U : Subgroup A, ⁅P, P⁆ ≤ U → U ≤ P →
    T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (U : Set A) → U = ⁅P, P⁆ ∨ U = P

@[expose] def OddOutcome {A : Type} [Group A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A) :
    Prop :=
  Nat.card P = p ^ 2 ∧
    ((StatedClassicalModel ↥L .PSL 3 p 1 ∨ Nonempty (↥L ≃* ↥(StatedSL 3 (ZMod p)))) ∨
      ∃ n : ℕ, Even n ∧ p ∣ 2 ^ n - 1 ∧ StatedClassicalModel ↥L .PSp 2 2 n ∧
        EmptyFaithfulMultiple.AutCyclic T P)

structure Facts134Odd : Prop where
  outCyclic : ∀ (A : Type) [Group A] [Finite A] (L U : Subgroup A) (p : ℕ), p.Prime → 5 ≤ p →
    SQTKHypCat A → L.Normal → CFSG.IsComponent L → IsPGroup p U →
    ∃ u ∈ U, U ≤ Subgroup.zpowers u ⊔ (L ⊔ Subgroup.centralizer (L : Set A))
  normal : ∀ (A : Type) [Group A] [Finite A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A),
    5 ≤ p → OddConfig p L P T → OddOutcome p L P T
  outAbelian : ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), SQTKHypCat A →
    CFSG.IsComponent L → A38Types ↥L → ∀ a ∈ Subgroup.normalizer (L : Set A),
      ∀ b ∈ Subgroup.normalizer (L : Set A), ⁅a, b⁆ ∈ L ⊔ Subgroup.centralizer (L : Set A)
  psl2Borel : ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (m p : ℕ) (y : A),
    SQTKHypCat A → p.Prime → 5 ≤ p → IsPSL 2 2 m ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) → y ∈ B → orderOf y = p →
      p ∣ 2 ^ m - 1
  psl2Even : ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (m p : ℕ) (y g : A),
    SQTKHypCat A → p.Prime → 5 ≤ p → IsPSL 2 2 m ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) → y ∈ B → orderOf y = p →
      g ∈ Subgroup.normalizer (L : Set A) → g ∈ Subgroup.normalizer (U : Set A) →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup A) : Set A) →
      (∃ k : ℕ, g ^ 2 ^ k = 1) → g * y * g⁻¹ ≠ y → Even m
  szLocal : ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (m p : ℕ) (y g : A),
    SQTKHypCat A → p.Prime → 5 ≤ p → IsSz m ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) → y ∈ B → orderOf y = p →
      g ∈ Subgroup.normalizer (L : Set A) → g ∈ Subgroup.normalizer (U : Set A) →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup A) : Set A) →
      (∃ k : ℕ, g ^ 2 ^ k = 1) → g * y * g⁻¹ = y
  j1Local : ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (p : ℕ) (y g : A),
    SQTKHypCat A → p.Prime → 5 ≤ p → IsSporadic .J1 ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) → y ∈ B → orderOf y = p →
      g ∈ Subgroup.normalizer (L : Set A) → g ∈ Subgroup.normalizer (U : Set A) →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup A) : Set A) →
      (∃ k : ℕ, g ^ 2 ^ k = 1) → g * y * g⁻¹ = y

end CFSG.Quasithin.H13.NQCore

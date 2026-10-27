module

public import CFSG.RankThree.PartOne.N143.JGood

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

@[expose] def Vof {G : Type} [Group G] (A J : Subgroup G) : Subgroup G :=
  Subgroup.closure {d : G | d ∈ J ⊓ Subgroup.centralizer (A : Set G) ∧ d ^ 3 = 1}

@[expose] def JFactX0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (J : Subgroup G),
    JGood p A c J → ∃ x ∈ J ⊓ torusNormalizer A, x ^ 3 = 1 ∧ ∃ a ∈ A, x * a * x⁻¹ ≠ a

@[expose] def JLemmaF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (J : Subgroup G),
    JGood p A c J → ∀ f : ℕ, p ∣ 2 ^ f - 1 →
    StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f →
    ∀ z ∈ Subgroup.normalizer (J : Set G) ⊓ torusNormalizer A, z ^ 3 = 1 →
      ∀ k : ℕ, k % p ≠ 1 → k ^ 3 % p = 1 → (∀ a ∈ Tof A J, z * a * z⁻¹ = a ^ k) → 3 ∣ f

@[expose] def JLemmaK2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (J : Subgroup G),
    JGood p A c J → ∀ w ∈ J ⊓ torusNormalizer A, w ^ 3 = 1 → (∃ a ∈ A, w * a * w⁻¹ ≠ a) →
    ∀ y ∈ Subgroup.normalizer (J : Set G) ⊓ torusNormalizer A, y ^ 3 = 1 →
    ∀ k : ℕ, k % p ≠ 1 → k ^ 3 % p = 1 → (∀ a ∈ Tof A J, y * a * y⁻¹ = w * a ^ k * w⁻¹) →
      ∃ l ∈ J, l⁻¹ * y * l ∈ Subgroup.normalizer (Tof A J : Set G) ∧
        ∀ a ∈ Tof A J, (l⁻¹ * y * l) * a * (l⁻¹ * y * l)⁻¹ = a ^ k

@[expose] def JLemmaA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (J : Subgroup G),
    JGood p A c J → ∀ f : ℕ, p ∣ 2 ^ f - 1 → 9 ∣ 2 ^ f - 1 →
    StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f →
    (CFSG.IsElementaryAbelian 3 (Vof A J) ∧ Nat.card (Vof A J) = 9) ∧
    ∀ w ∈ J ⊓ torusNormalizer A, (∀ a ∈ A, w ^ 3 * a * (w ^ 3)⁻¹ = a) → (∃ a ∈ A, w * a * w⁻¹ ≠ a) →
    ∀ y ∈ Subgroup.normalizer (J : Set G) ⊓ torusNormalizer A, ∀ k : ℕ,
      (∀ a ∈ A, y * a * y⁻¹ = w * a ^ k * w⁻¹) → ∃ v ∈ Vof A J, y * v * y⁻¹ ≠ v

@[expose] def JLemmaKt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (J : Subgroup G),
    JGood p A c J → ∀ R : Subgroup G, IsPGroup 3 R →
    R ≤ Subgroup.normalizer (J : Set G) ⊓ torusNormalizer A →
    (∀ u ∈ R, ∃ k : ℕ, ∀ a ∈ Tof A J, u * a * u⁻¹ = a ^ k) →
      ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ S ≤ J ∧ R ≤ Subgroup.normalizer (S : Set G)

@[expose] def Nt {G : Type} [Group G] (A J : Subgroup G) (t : MulAut A) : Subgroup G :=
  J ⊓ Subgroup.centralizer (autFixedInG A t : Set G)

@[expose] def Kof {G : Type} [Group G] (A J : Subgroup G) (t : MulAut A) : Subgroup G :=
  ⁅Nt A J t, Nt A J t⁆

@[expose] def JLemmaKt1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (J : Subgroup G),
    JGood p A c J → ∀ t ∈ reflectionSet p A, t ∈ torusImage A J → ∀ f : ℕ, p ∣ 2 ^ f - 1 →
    StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f →
      IsSimpleGroup (Kof A J t) ∧ Nat.card (Kof A J t) = 2 ^ f * (2 ^ (2 * f) - 1) ∧
        autMovedInG A t ≤ Kof A J t

@[expose] def JLemma42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (J : Subgroup G),
    JGood p A c J → ∀ f : ℕ, p ∣ 2 ^ f - 1 →
    StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f → 2 ^ f % 3 = 2 →
    ∀ z ∈ Subgroup.normalizer (J : Set G) ⊓ torusNormalizer A, z ^ 3 = 1 →
    ∀ k : ℕ, k % p ≠ 1 → k ^ 3 % p = 1 → (∀ a ∈ Tof A J, z * a * z⁻¹ = a ^ k) →
    ∀ g ∈ Subgroup.normalizer (J : Set G), g ∈ Subgroup.centralizer (A : Set G) →
      (∃ n : ℕ, g ^ (3 ^ n) = 1) → g ∈ Subgroup.centralizer (J : Set G)

@[expose] def JLemmaB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (J : Subgroup G),
    JGood p A c J → ∀ f : ℕ, p ∣ 2 ^ f - 1 →
    StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f → 2 ^ f % 3 = 2 →
    ¬ 3 ∣ Nat.card (J ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ∧
    ∀ x ∈ J ⊓ torusNormalizer A, x ^ 3 = 1 → (∃ a ∈ A, x * a * x⁻¹ ≠ a) →
      ∃ U : Subgroup G, (∀ u : G, u ∈ U ↔
          u ∈ J ⊓ Subgroup.centralizer ({x} : Set G) ∧ ∃ n : ℕ, u ^ (3 ^ n) = 1) ∧
        IsCyclic ↥U ∧ Nat.card U = 3 ^ (Nat.card J).factorization 3

@[expose] def JFacts : Prop :=
  JFactX0 ∧ JLemmaF ∧ JLemmaK2 ∧ JLemmaA ∧ JLemmaKt ∧ JLemmaKt1 ∧ JLemma42 ∧ JLemmaB

end CFSG.RankThree.PartOne.N143

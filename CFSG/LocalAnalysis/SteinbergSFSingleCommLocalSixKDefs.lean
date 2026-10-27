module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommParts

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section KDefs

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] def K1Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ v ∈ Vtor φ t i i, t * v * (t * v) = 1 → ∃ x ∈ Vtor φ t i i, x⁻¹ * t * x = t * v

@[expose] def K2Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ m ∈ Mhat φ t i i, t * m * (t * m) = 1 → ∃ x ∈ Mhat φ t i i, x⁻¹ * t * x = t * m

@[expose] def K3Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ x ∈ S φ t i, t * x * (t * x) = 1 → ∃ s ∈ S φ t i, s⁻¹ * t * s = t * x

@[expose] def K4aConcl (φ : L ≃* antiSp K) (i : Axis) : Prop :=
  ∀ x ∈ Ytor φ i, x * x = 1 → ∃ y ∈ Ytor φ i, y⁻¹ * x * y ∈ U φ i

@[expose] def K4bConcl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ x ∈ Dstar φ t i, x * x = 1 → x ∈ Mhat φ t i i ∨ x ∈ Mhat φ t i i.swap

@[expose] def K4Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ x ∈ S φ t i, x * x = 1 →
    ∃ g : G, g⁻¹ * x * g ∈ Mhat φ t i i ∨ g⁻¹ * x * g ∈ Mhat φ t i i.swap

@[expose] def K5Concl (n : ℕ) (φ : L ≃* antiSp K) (t : G) : Prop :=
  ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → (∀ x ∈ E, x * x = 1) →
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ 2 ^ (3 * n + 1)

@[expose] def K6Concl (n : ℕ) (φ : L ≃* antiSp K) (t : G) : Prop :=
  ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer ({t} : Set G) →
    Nat.card R ≤ 4 * n * Nat.card K ^ 4

@[expose] def K7Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ g : G, g⁻¹ * t * g ∉ Mhat φ t i i

@[expose] def K8Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ g : G, g⁻¹ * t * g ∉ Mhat φ t i i.swap

@[expose] def K9Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ g : G, g⁻¹ * t * g ∉ S φ t i

@[expose] def K11Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  S φ t i ⊓ centralizer ({t} : Set G) = P φ

end KDefs

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard

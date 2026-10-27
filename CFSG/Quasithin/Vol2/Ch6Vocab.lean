module

public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

abbrev ch6ZS (T L V : Subgroup G) : Subgroup G :=
  V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)

abbrev ch6S (T L V : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)

abbrev ch6Q (T V : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.centralizer (V : Set G)

abbrev ch6MV (M V : Subgroup G) : Subgroup G :=
  M ⊓ Subgroup.normalizer (V : Set G)

@[expose] def IsInvolutoryFieldAut (L : Subgroup G) (t : G) : Prop :=
  t ∈ Subgroup.normalizer (L : Set G) ∧
    (∀ x ∈ L, t ^ 2 * x * (t ^ 2)⁻¹ * x⁻¹ ∈ pCoreOf 2 L) ∧
    ¬ ∃ y ∈ L, ∀ x ∈ L, (t * x * t⁻¹) * (y * x * y⁻¹)⁻¹ ∈ pCoreOf 2 L

@[expose] def thompsonJk (k : ℕ) (T : Subgroup G) : Subgroup G :=
  ⨆ (A : Subgroup G) (_ : A ≤ T ∧ IsElemAbelian 2 A ∧
      ∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card B ≤ 2 ^ k * Nat.card A), A

@[expose] def IsElemAbelianMod (U W : Subgroup G) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ W ∧ u ^ 2 ∈ W

@[expose] def IsO2Trivial (X Y : Subgroup G) : Prop :=
  ∀ P : Subgroup G, P ≤ X → X ≤ Subgroup.normalizer (P : Set G) →
    (∀ p ∈ P, ∃ k : ℕ, p ^ 2 ^ k ∈ Y) → P ≤ Y

@[expose] def IsReducedMod (H U W : Subgroup G) : Prop :=
  W ≤ U ∧ U ≤ H ∧ H ≤ Subgroup.normalizer (U : Set G) ∧ H ≤ Subgroup.normalizer (W : Set G) ∧
    IsElemAbelianMod U W ∧ IsO2Trivial H (centralizerMod W H U)

end CFSG.Quasithin.H13

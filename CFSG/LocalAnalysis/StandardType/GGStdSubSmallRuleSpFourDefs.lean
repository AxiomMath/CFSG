module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinHigh

public section

namespace CFSG.StandardType.SpFour

open CFSG.Assembly TableB

section Defs

variable {G : Type*} [Group G]

@[expose] def layerC (y : G) : Subgroup G :=
  LargeEvenLayer (Subgroup.centralizer ({y} : Set G))

@[expose] def EndNodeAt (Ã : Subgroup G) (y : G) : Prop :=
  IsComponentOf (layerC y) (Subgroup.centralizer ({y} : Set G)) ∧
    ∀ s ∈ Ã, ((∀ j ∈ layerC y, s * j = j * s) ↔ s ∈ Subgroup.zpowers y)

@[expose] def ConclAt (Ã : Subgroup G) (y : G) : Prop :=
  ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ layerC y ∧
    (∀ s ∈ Ã, ∀ u ∈ U, s * u * s⁻¹ ∈ U) ∧
    ∃ t ∈ layerC y, t ^ 3 = 1 ∧ (∀ s ∈ Ã, s * t = t * s) ∧
      t ∈ Subgroup.normalizer (U : Set G) ∧ ∃ j ∈ layerC y, t * j ≠ j * t

@[expose] def RuleAt (Ã : Subgroup G) (y : G) : Prop :=
  (∃ z ∈ Ã, z ≠ 1 ∧ EndNodeAt Ã z ∧ ¬ LargeEvenSmall (layerC z)) → ¬ LargeEvenSmall (layerC y)

end Defs

end CFSG.StandardType.SpFour

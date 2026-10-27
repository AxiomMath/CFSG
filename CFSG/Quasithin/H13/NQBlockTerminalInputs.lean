module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.NQSetupDefs

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped commutatorElement

@[expose] def NonquasisimpleTIEscapingResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    (∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M) →
    normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧ X ≤ T} :
      Subgroup G) : Set G) ≤ M →
    ∃ (H Y : Subgroup G) (_ : (Y.subgroupOf H).Normal), T ≤ H ∧ Y ≤ H ∧ Group.IsPerfect Y ∧
      IsPGroup 2 (H ⧸ Y.subgroupOf H) ∧ IsSimpleGroup (Y ⧸ CFSG.pCore 2 Y) ∧
      (∃ a b : Y ⧸ CFSG.pCore 2 Y, a * b ≠ b * a) ∧ ¬ Y ≤ M ∧
      CFSG.pRank 2 (H ⧸ CFSG.pCore 2 H) ≤ 2

@[expose] def ConfigurationFourGroupObstruction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ B : Subgroup G, B ≤ M → CFSG.IsElementaryAbelian 2 B → Nat.card B = 4 →
      ∃ b ∈ B, b ≠ 1 ∧ ∀ l ∈ L, ⁅l, b⁆ ∈ (CFSG.solvableRadical ↥L).map L.subtype

end CFSG.Quasithin.H13.NQBlock

module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def IsQSNormalIn {K : Type} [Group K] (X S : Subgroup K) : Prop :=
  X ≤ S ∧ (X.subgroupOf S).Normal ∧ CFSG.IsQuasisimple X

@[expose] def Stroth41iiStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    (¬ ∃ X : Subgroup (Mbar M Q), X ≤ bar M Q (Lgen M (LB M Q B)) ∧
      (X.subgroupOf (bar M Q (Lgen M (LB M Q B)))).Normal ∧
      IsSLModel 2 (Nat.card Z) ↥X) →
    ∀ (X₁ X₂ : Subgroup (Mbar M Q)), IsQSNormalIn X₁ (bar M Q (Lgen M (LB M Q B))) →
      IsQSNormalIn X₂ (bar M Q (Lgen M (LB M Q B))) → X₁ = X₂

@[expose] def Stroth42Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    layer (Mbar M Q) ≠ ⊥ →
    (¬ ∃ X : Subgroup (Mbar M Q), X ≤ layer (Mbar M Q) ∧
      (X.subgroupOf (layer (Mbar M Q))).Normal ∧ IsSLModel 2 (Nat.card Z) ↥X) →
    CFSG.IsQuasisimple ↥(layer (Mbar M Q))

@[expose] def Stroth43Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    (∃! Y : Subgroup (Mbar M Q), IsComponent Y ∧ IsSLModel 2 (Nat.card Z) ↥Y) →
    ¬ IsSLModel 2 (Nat.card Z) ↥(layer (Mbar M Q)) →
    ∃ X Y : Subgroup (Mbar M Q), X ⊔ Y = layer (Mbar M Q) ∧ X ⊓ Y = ⊥ ∧
      (∀ x ∈ X, ∀ y ∈ Y, Commute x y) ∧ CFSG.IsQuasisimple ↥X ∧
      IsSLModel 2 (Nat.card Z) ↥Y

@[expose] def Stroth44Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (A : Subgroup (Mbar M Q)), A ≤ bar M Q (H0 M Z) →
      bar M Q (LB M Q B) ≤ Subgroup.normalizer (A : Set (Mbar M Q)) →
      Odd (Nat.card A) → A = ⊥

end CFSG.RankThree.GF2n.Stroth80

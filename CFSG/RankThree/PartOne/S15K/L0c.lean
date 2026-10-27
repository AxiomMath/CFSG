module

public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.S12.Facts

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def KF158L0cRowFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Four p E A (lieGenerated p E) →
    ∀ b ∈ E, b ≠ 1 → ∀ z ∈ Subgroup.centralizer ({b} : Set G),
      ∀ Y ∈ thetaCompZeroE p E, Y ∈ thetaComponentsAt p b → Y ≤ lieGenerated p E →
        conjBy z Y ∈ thetaCompZeroE p E

@[expose] def KF158L0cRowFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ b ∈ E, b ≠ 1 → ∀ z ∈ Subgroup.centralizer ({b} : Set G),
      ∀ Y ∈ thetaCompZeroE p E, Y ∈ thetaComponentsAt p b → Y ≤ lieGenerated p E →
        conjBy z Y ∈ thetaCompZeroE p E

end CFSG.RankThree.PartOne.S15K

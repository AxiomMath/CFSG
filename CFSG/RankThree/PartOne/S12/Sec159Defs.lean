module

public import CFSG.RankThree.PartOne.S12.Facts

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

@[expose] def KF159Z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    E = A → ∀ X ∈ thetaCompE p E, X ∉ thetaCompZeroE p E →
      ¬ p ∣ Nat.card ↥(Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X))

@[expose] def Node159Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    E = A → ∀ X ∈ thetaCompE p E, X ≤ lieNormalizer p E

@[expose] def Node159Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompE p E, X ≤ lieNormalizer p E

end CFSG.RankThree.PartOne

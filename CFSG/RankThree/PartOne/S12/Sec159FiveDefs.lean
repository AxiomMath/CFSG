module

public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.PartOne.S12.Facts

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

@[expose] def KF159ZFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompE p E, X ∉ thetaCompZeroE p E →
      ¬ p ∣ Nat.card ↥(Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X))

@[expose] def KF159RankFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompE p E,
      CFSG.twoLocalOddRank ((↥X ⧸ aschbacherSolvableCore p ↥X) ⧸
        Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)) ≤ 3

@[expose] def KF159Sz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompE p E,
      Census3.IsoLie ((↥X ⧸ aschbacherSolvableCore p ↥X) ⧸
        Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)) (.suzuki 2) →
      ∀ e ∈ E, ∃ y ∈ X, y⁻¹ * e ∈ thetaQuotientCentralizer p ⊤ X

end CFSG.RankThree.PartOne

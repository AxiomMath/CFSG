module

public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.RankThree.PartOne.S12.Facts13

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def KF141 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f → E = A →
    (∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J) →
    (∀ t ∈ reflectionSet p E, t ∈ torusImage E L → KFAt p E f t) ∧
    (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ t ∈ reflectionSet p E,
      t ∈ torusImage E L → s ≠ t → KFPairL p E f s t) ∧
    (∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → s * t = t * s →
      kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧
        kZero p E s ⊓ kZero p E t = ⊥)

end CFSG.RankThree.PartOne

module

public import CFSG.RankThree.PartOne.N1322.Statements
public import CFSG.RankThree.PartOne.S12.Facts13

public section

namespace CFSG.RankThree.PartOne.NF7J

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N1322

@[expose] def PairMember : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
    RowModel p L 7 →
    ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s * t ≠ t * s →
      (∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
        conjAut E w hw * s * (conjAut E w hw)⁻¹ ∈ torusImage E L) →
      (∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
        conjAut E w hw * t * (conjAut E w hw)⁻¹ ∈ torusImage E L) →
      ∃ J ∈ thetaCompZeroStarE p E, s ∈ torusImage E J ∧ t ∈ torusImage E J

end CFSG.RankThree.PartOne.NF7J

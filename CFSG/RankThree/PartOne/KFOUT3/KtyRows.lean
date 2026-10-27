module

public import CFSG.RankThree.PartOne.N1322.Statements

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N1322

@[expose] def KF1322KtyRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
    RowModel p L r →
    ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, DiffClass E L t s →
      ∀ (g : G) (hg : g ∈ Subgroup.normalizer (E : Set G)),
        conjAut E g hg * t * (conjAut E g hg)⁻¹ ≠ s

theorem kf1322Kty_of_rows (h3 : KF1322KtyRow 3) (h4 : KF1322KtyRow 4) (h5 : KF1322KtyRow 5)
    (h6 : KF1322KtyRow 6) (h8 : KF1322KtyRow 8) : KF1322Kty := by
  intro G _ _ p A c L E h12 hF12 hF13 hno5 hEA hL3 hrow t ht s hs hts g hg
  rcases hrow with hm | hm | hm | hm | hm
  · exact h3 G p A c L E h12 hF12 hF13 hno5 hEA hL3 hm t ht s hs hts g hg
  · exact h4 G p A c L E h12 hF12 hF13 hno5 hEA hL3 hm t ht s hs hts g hg
  · exact h5 G p A c L E h12 hF12 hF13 hno5 hEA hL3 hm t ht s hs hts g hg
  · exact h6 G p A c L E h12 hF12 hF13 hno5 hEA hL3 hm t ht s hs hts g hg
  · exact h8 G p A c L E h12 hF12 hF13 hno5 hEA hL3 hm t ht s hs hts g hg

end CFSG.RankThree.PartOne.KFOUT3

module

public import CFSG.RankThree.PartOne.KF.Reduction123

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def KF123ClassifyTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123Generic p L A₀ F →
    (∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧
      CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n 2 f) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ 12 ∧ r ≠ 11 ∧ RowModel p L r

theorem kf123Classify_of_tags (h : ∀ t : StatedLieTag, KF123ClassifyTag t) : KF123Classify := by
  intro G _ _ p L A₀ F hT
  obtain ⟨t, n, f, hadm, hm⟩ := hT.evenLie
  exact h t G p L A₀ F hT ⟨n, f, hadm, hm⟩

theorem kf123ClassifyTag_twistedG2 : KF123ClassifyTag .twistedG2 := by
  intro G _ _ p L A₀ F hT hLie
  obtain ⟨n, f, hadm, -⟩ := hLie
  exact absurd hadm.2.2.2.1 (by norm_num)

theorem kf123ClassifyTag_POmegaOdd : KF123ClassifyTag .POmegaOdd := by
  intro G _ _ p L A₀ F hT hLie
  obtain ⟨n, f, hadm, -⟩ := hLie
  exact absurd rfl hadm.2.2.2

end CFSG.RankThree.PartOne

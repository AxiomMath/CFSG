module

public import CFSG.RankThree.PartOne.S11d.LowRank

public section

namespace CFSG.RankThree.PartOne.TCX

open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem threeCompBL_of_highRank {t : StatedLieTag} (h : ∀ n, ¬ LowRank t n) : ThreeCompBL t :=
  fun _ _ _ _ _ _ _ _ n _ _ _ hlow => (h n hlow).elim

theorem fixedRankTL_of_highRank {t : StatedLieTag} (h : ∀ n, ¬ LowRank t n) : FixedRankTL t :=
  fun _ _ _ _ _ _ _ _ n _ _ _ hlow => (h n hlow).elim

theorem not_lowRank_highTags : ∀ t : StatedLieTag,
    (t = .POmegaPlus ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
      ∀ n, ¬ LowRank t n := by
  intro t ht n
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> exact fun h => h

theorem threeCompBL_POmegaPlus : ThreeCompBL .POmegaPlus :=
  threeCompBL_of_highRank (not_lowRank_highTags _ (Or.inl rfl))

theorem fixedRankTL_POmegaPlus : FixedRankTL .POmegaPlus :=
  fixedRankTL_of_highRank (not_lowRank_highTags _ (Or.inl rfl))

theorem threeCompBL_F4 : ThreeCompBL .F4 :=
  threeCompBL_of_highRank (not_lowRank_highTags _ (Or.inr (Or.inl rfl)))

theorem fixedRankTL_F4 : FixedRankTL .F4 :=
  fixedRankTL_of_highRank (not_lowRank_highTags _ (Or.inr (Or.inl rfl)))

theorem threeCompBL_E6 : ThreeCompBL .E6 :=
  threeCompBL_of_highRank (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inl rfl))))

theorem fixedRankTL_E6 : FixedRankTL .E6 :=
  fixedRankTL_of_highRank (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inl rfl))))

theorem threeCompBL_E7 : ThreeCompBL .E7 :=
  threeCompBL_of_highRank (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

theorem fixedRankTL_E7 : FixedRankTL .E7 :=
  fixedRankTL_of_highRank (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

theorem threeCompBL_E8 : ThreeCompBL .E8 :=
  threeCompBL_of_highRank
    (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

theorem fixedRankTL_E8 : FixedRankTL .E8 :=
  fixedRankTL_of_highRank
    (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

theorem threeCompBL_twistedE6 : ThreeCompBL .twistedE6 :=
  threeCompBL_of_highRank
    (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

theorem fixedRankTL_twistedE6 : FixedRankTL .twistedE6 :=
  fixedRankTL_of_highRank
    (not_lowRank_highTags _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

end CFSG.RankThree.PartOne.TCX

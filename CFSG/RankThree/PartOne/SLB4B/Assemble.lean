module

public import CFSG.RankThree.PartOne.SLB4B.Indices
public import CFSG.RankThree.PartOne.N143.SecRankRest

public section

namespace CFSG.RankThree.PartOne.SLB4B

open TauCeti CFSG.RankThree.PartOne.SRC CFSG.RankThree.PartOne.N143

section Cover


theorem rankFourCover_of_lowTwoRank (i : CFSGIndex) (hi : IsLieLowTwoRankIndex i) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ RankFourCover p i.Group := by
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases li <;> first | exact (hi : False).elim | skip
    ·
      rename_i r q
      have hq : (r = 4 ∧ q.p ≠ 2) ∨ (r = 5 ∧ q.card % 4 = 3) := hi
      rcases hq with ⟨hr, hq2⟩ | ⟨hr, hq⟩
      · subst hr
        exact ⟨q.p, q.prime_p, hq2, rankFourCover_typeA 4 q hv le_rfl hq2⟩
      · subst hr
        have hq2 : q.p ≠ 2 := p_ne_two_of_card_odd q (by omega)
        exact ⟨q.p, q.prime_p, hq2, rankFourCover_typeA 5 q hv (by norm_num) hq2⟩
    ·
      rename_i r q
      have hq : (r = 4 ∧ q.p ≠ 2) ∨ (r = 5 ∧ q.card % 4 = 1) := hi
      rcases hq with ⟨hr, hq2⟩ | ⟨hr, hq⟩
      · subst hr
        exact rankFourCover_typeTwistedA 4 q hv le_rfl hq2
      · subst hr
        exact rankFourCover_typeTwistedA 5 q hv (by norm_num)
          (p_ne_two_of_card_odd q (by omega))
    ·
      rename_i r q
      have hr : r = 3 := hi
      subst hr
      exact rankFourCover_typeC q hv
  · exact (hi : False).elim

theorem noLowTwoRankSectionFor_lowTwoRank : NoLowTwoRankSectionFor IsLieLowTwoRankIndex :=
  noLowTwoRankSectionFor_of_rankFourCover rankFourCover_of_lowTwoRank

end Cover

end CFSG.RankThree.PartOne.SLB4B

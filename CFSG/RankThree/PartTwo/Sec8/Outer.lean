module

public import CFSG.RankThree.PartTwo.Sec8.Notation
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}

theorem Hyp81.inducesOuterTheta (h : Hyp81 G A c L a) : InducesOuterTheta a L := by
  rcases h.inducesStdKind with h' | h'
  · exact KFacts.InducesStdKind.inducesOuterTheta L h' (by decide)
  · exact KFacts.InducesStdKind.inducesOuterTheta L h' (by decide)

theorem Hyp81.induced_pow_three (h : Hyp81 G A c L a) :
    thetaQuotMulAut L (compAction L ⟨a, h.a_mem_normalizer⟩) ^ 3 = 1 := by
  have h1 : (⟨a, h.a_mem_normalizer⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using h.mem_partTwoF.1.2 a h.a_mem)
  rw [← map_pow, ← map_pow, h1, map_one, map_one]

theorem Hyp81.not_isInnerAut_induced (h : Hyp81 G A c L a) :
    ¬ KFacts.IsInnerAut (thetaQuotMulAut L (compAction L ⟨a, h.a_mem_normalizer⟩)) := by
  obtain ⟨hx, hx'⟩ := h.inducesOuterTheta
  exact hx'

end CFSG.RankThree.PartTwo.Sec8

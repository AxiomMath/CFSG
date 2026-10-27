module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddThree
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Odd
import CFSG.CGT.PushingUpLit.Transport
import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem facts_of_mem_conjSetOf (S : SliceCore D L D₃ Y H) {K : Subgroup G}
    (hK : K ∈ conjSetOf D.M L) : Shape919 (Bar2 K) := by
  obtain ⟨g, -, rfl⟩ := hK
  obtain ⟨e⟩ := uc22p20d_bar2_conj g L
  exact S.facts_L.of_mulEquiv e

theorem ncard_conjSetOf_le_two (h82 : F08.R82 D) (S : SliceCore D L D₃ Y H)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) : (conjSetOf D.M L).ncard ≤ 2 :=
  UC22.R8107Odd.ncard_conjSetOf_le_two h82 hnsp S.L_mem S.pRank_three_L

theorem mem_normalizer_L_of_odd (h82 : F08.R82 D) (S : SliceCore D L D₃ Y H)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {g : G} (hg : g ∈ D.M) (hodd : Odd (orderOf g)) :
    g ∈ normalizer (L : Set G) :=
  UC22.R8107Odd.mem_normalizer_of_odd h82 hnsp S.L_mem S.pRank_three_L hg hodd

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

module

public import CFSG.RankThree.PartTwo.Sec17.Item17Setup
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsKS

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

variable {G : Type} [Group G] [Finite G]

theorem claim17M_of_hasFaithfulE9 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h152 : Item152 A (lB A))
    (hE : ∀ Y₀ ∈ scriptY0Star A (lB A), scriptY0Star A (lB A) = {Y₀} → HasFaithfulE9 Y₀) :
    Claim17M A (lB A) := fun Y₀ hY₀ hstar =>
  maximalTwoLocalsContaining_eq_of_hasFaithfulE9 h h152 hY₀ (hE Y₀ hY₀ hstar)

theorem claim17M_of_item163 {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h163 : Item163 A (lB A) c L) (h152 : Item152 A (lB A)) : Claim17M A (lB A) :=
  claim17M_of_hasFaithfulE9 h.toSec14Std h152 fun Y₀ hY₀ _ =>
    hasFaithfulE9_of_le_lA h.toSec14Std (h163 Y₀ hY₀).2.2.2.1

end CFSG.RankThree.PartTwo.Sec17

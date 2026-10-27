module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List863
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CenterCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

variable {G : Type} [Group G] [Finite G]

theorem center_le_of_list864_of_not_commutator
    {L X P : Subgroup G}
    (h : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List864 L X P)
    (hnot : ¬ ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L) :
    X ≤ (Subgroup.center ↥P).map P.subtype := by
  unfold List864 at h
  rcases h with ⟨-, hle⟩ | ⟨-, hle⟩ | ⟨-, hle⟩ | ⟨-, -, hZ⟩
  · exact absurd hle hnot
  · exact absurd hle hnot
  · exact absurd hle hnot
  · exact hZ

theorem commutator_eq_bot_of_list864
    {L Q X P : Subgroup G}
    (h : List864 L X P)
    (hnot : ¬ ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L)
    (hQP : Q ≤ P) :
    ⁅Q, X⁆ = ⊥ :=
  commutator_eq_bot_of_le_center hQP (center_le_of_list864_of_not_commutator h hnot)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

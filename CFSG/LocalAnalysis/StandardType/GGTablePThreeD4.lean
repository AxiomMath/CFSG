module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRank
import CFSG.LocalAnalysis.StandardType.GGTablePThreeDatum
import CFSG.LocalAnalysis.StandardType.GGD4OddCentLSide

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggMarkingAll_not_of_not {X : Type*} [Group X] {S : LargeEvenLabel → Prop}
    (h : ¬ LargeEvenMarking X fun lab _ _ _ _ _ => S lab) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => ¬ S lab := by
  intro P hP
  obtain ⟨hX, lab, hlab, hraw⟩ := hP
  by_cases hS : S lab
  · exact absurd ⟨hX, lab, hlab,
      largeEvenRawDatum_mono (fun R _ I F hh => ⟨hh.1, hh.2.1, hh.2.2.imp fun _ _ => hS⟩) hraw⟩ h
  · exact ⟨hX, lab, hlab,
      largeEvenRawDatum_mono (fun R _ I F hh => ⟨hh.1, hh.2.1, hh.2.2.imp fun _ hθ => ⟨hθ, hS⟩⟩) hraw⟩

section D4

theorem ggStdSubD4Input_of_tablePThree
    (h : GGTablePThreeD4OddKnown) : GGStdSubD4Input := by
  intro G _ _ B x L D J hI hDJ hm hJ
  obtain ⟨hNL, δ, hd⟩ := exists_ggTablePThree_datum hI hDJ
  have hJL : J ≤ L := le_of_stdSub_left hDJ
  have hJ' : LargeEvenMarking ↥(J.subgroupOf L) (fun lab _ _ _ _ _ =>
      lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n) :=
    GGTablePThree.largeEvenMarking_subgroupOf hJL hJ
  have hcomm : commutator ↥L = ⊤ := hI.2.2.2.2.2.2.2.1.1
  have hKG := h (X := ↥L) hcomm (ggAutsOf L B hNL) δ (J.subgroupOf L) hd hJ'
  have hnotD6 : ¬ LargeEvenMarking ↥L (fun lab _ _ _ _ _ =>
      lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) := by
    intro hM
    exact absurd (le_trans (six_le_twoLocalRank_of_tablePThree_D6 hI hM) hm) (by decide)
  have hnotTwD7 : ¬ LargeEvenMarking ↥L (fun lab _ _ _ _ _ =>
      lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) := by
    intro hM
    exact absurd (le_trans (seven_le_twoLocalRank_of_tablePThree_twD7 hI hM) hm) (by decide)
  have hComb := ggMarkingAll_and (ggMarkingAll_and hKG (ggMarkingAll_not_of_not hnotD6))
    (ggMarkingAll_not_of_not hnotTwD7)
  refine ggMarkingAll_mono (fun lab R _ I F θ hh hsplit => ?_) hComb
  obtain ⟨⟨himp, hnc⟩, hnd⟩ := hh
  rcases himp hsplit with ⟨hA, _⟩ | hB | hC | hD
  · exact Or.inr hA
  · exact Or.inl hB
  · exact absurd hC hnc
  · exact absurd hD hnd

end D4

end CFSG.StandardType

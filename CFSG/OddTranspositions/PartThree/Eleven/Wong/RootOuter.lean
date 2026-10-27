module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootData
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentOuterElt
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentYEq

public section

namespace CFSG.OddTranspositions.PartThree.Wong

variable {G : Type} [Group G]

theorem SplitData.exists_outer [Finite G] (D : SplitData G) : ∃ s, D.Outer s := by
  obtain ⟨hX, hN, hAv, hCt⟩ := D.second_centralizer_card_and_diagonal_normal
  obtain ⟨s, hs, hs2, ht, hXeq, hA, hD, hpsi⟩ := D.normalized_outer_element
  obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := D.normalized_y_equations hs2 ht hpsi
  exact ⟨s, ⟨hX, hN, hAv, hCt, hs, hs2, ht, hXeq, hA, hD, hpsi, y1, y2, y3, y4, y5, y6, y7⟩⟩

end CFSG.OddTranspositions.PartThree.Wong

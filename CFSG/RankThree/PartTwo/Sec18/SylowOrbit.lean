module

public import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Late.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late


theorem item184_3_of (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2) : Item184_3 := by
  intro G _ _ A M H c hH K hK
  obtain ⟨-, d, hd3, hdcen⟩ := h184 G A M hH.toSec18Std K hK
  have hK' : Sec18H G A M K d := ⟨hH.toSec18Std, hK, hdcen⟩
  have hP := planeQ8_of_sec18H h1812 h184 hH
  have hP' := planeQ8_of_sec18H h1812 h184 hK'
  obtain ⟨-, halt⟩ := wStar_structure_of_sec18H h1812 h184 h1842 hH
  obtain ⟨hWB', -⟩ := wStar_structure_of_sec18H h1812 h184 h1842 hK'
  have hcard_c : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_three_of_sec18H h184 hH]
  rw [hK'.centralizer_eq]
  rcases halt with hWc | ⟨-, -, -, horb, -⟩
  ·
    rcases Sec13.eq_of_le_of_le_normalizer hP'.isElemAbelian hP'.card_eq hP'.mem hP'.eq_sup
        hP'.not_mem hP'.card_plane hP'.commute hP'.irreducible (Subgroup.zpowers_le.mpr hP.mem)
        (hP'.le_normalizer.trans hWc) hP'.le_normalizer_plane with h | h | h | h
    · rw [h, Subgroup.card_bot] at hcard_c
      norm_num at hcard_c
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [map_conj_one, h]
    · rw [h, hP'.card_plane] at hcard_c
      norm_num at hcard_c
    · rw [h, hP'.card_eq] at hcard_c
      norm_num at hcard_c
  ·
    have hBK : A ⊓ inSubgroup perfectResidual K = A ⊓ inSubgroup perfectResidual H := by
      have h9 := hP'.card_plane
      rcases Sec13.eq_of_le_of_le_normalizer hP.isElemAbelian hP.card_eq hP.mem hP.eq_sup
          hP.not_mem hP.card_plane hP.commute hP.irreducible inf_le_left
          (hP.le_normalizer.trans hWB') hP.le_normalizer_plane with h | h | h | h
      · rw [h, Subgroup.card_bot] at h9
        norm_num at h9
      · rw [h, hcard_c] at h9
        norm_num at h9
      · exact h
      · rw [h, hP.card_eq] at h9
        norm_num at h9
    have hdP : Subgroup.zpowers d ∈ Sec13.pointsOff A (A ⊓ inSubgroup perfectResidual H) := by
      refine ⟨Subgroup.zpowers_le.mpr hP'.mem, by rw [Nat.card_zpowers, hd3], fun h => ?_⟩
      apply hP'.not_mem
      rw [hBK]
      exact Subgroup.zpowers_le.mp h
    rw [← horb] at hdP
    obtain ⟨w, hw, hwd⟩ := hdP
    exact ⟨w, hw, by rw [hwd]⟩

end CFSG.RankThree.PartTwo.Sec18

module

public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
import CFSG.RankThree.PartOne.N143.AltRank
import CFSG.RankThree.PartOne.N143.AltTwoRank
import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.GH74.Generic.GKFCover
import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup

theorem oddCentralCoverRank3For_alternating :
    OddCentralCoverRank3For IsAlternatingIndex := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  cases i with
  | alternating n hn =>
    obtain ⟨hker, hYq, ⟨hcongr⟩⟩ := central_cover_quasisimple hperf hnonab φ hφ hcent
    have h3Z : 3 ∣ Nat.card (center Y) := by rw [hker]; exact h3dvd
    have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hYq (hcongr.trans e)
    rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn).2] at hdvd
    have h67 : n = 6 ∨ n = 7 := by
      by_contra h
      simp only [h, ↓reduceIte] at hdvd
      have := h3Z.trans hdvd
      omega
    have hA : evenRank (alternatingGroup (Fin n)) ≤ 3 := evenRank_alternating_le_three (by omega)
    rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank,
      Census3.twoLocalOddRank_eq_of_mulEquiv e,
      ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
    exact hA
  | cyclic p hp => exact absurd hi (by simp [IsAlternatingIndex])
  | lie d => exact absurd hi (by simp [IsAlternatingIndex])
  | sporadic s => exact absurd hi (by simp [IsAlternatingIndex])

theorem lowTwoRankSectionFor_alternating :
    LowTwoRankSectionFor IsAlternatingIndex := by
  intro L _ _ hK he H M _ _ hM π hπ hU ⟨i, hi, ⟨e⟩⟩
  cases i with
  | alternating n hn =>
    have hn11 : n ≤ 11 := by
      by_contra h
      obtain ⟨U, hU', hUc⟩ := exists_isElementaryAbelian_two_pow_five (n := n) (by omega)
      obtain ⟨hU'', hc⟩ := CFSG.RankThree.Coprime.isElementaryAbelian_map_mulEquiv e.symm hU'
      exact hU ⟨U.map e.symm.toMonoidHom, hU'', hc.trans hUc⟩
    refine ⟨?_, ?_⟩
    · rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank,
        Census3.twoLocalOddRank_eq_of_mulEquiv e,
        ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
      exact evenRank_alternating_le_three hn11
    · intro ℓ hℓ hℓ7 hdvd
      have hdvd' := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hM e
      rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn).2] at hdvd'
      have hle := Nat.le_of_dvd (by split_ifs <;> norm_num) (hdvd.trans hdvd')
      split_ifs at hle <;> omega
  | cyclic p hp => exact absurd hi (by simp [IsAlternatingIndex])
  | lie d => exact absurd hi (by simp [IsAlternatingIndex])
  | sporadic s => exact absurd hi (by simp [IsAlternatingIndex])

end CFSG.RankThree.PartOne.N143

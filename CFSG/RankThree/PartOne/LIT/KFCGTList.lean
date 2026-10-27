module

public import CFSG.RankThree.PartOne.S12.PushingUp
import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.RankThree.PartOne.LIT.RankPSL3
import CFSG.RankThree.PartOne.LIT.RankSuzuki
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.LIT

theorem kfCGTList : KFCGTList := by
  intro G _ _ _ _ hfam
  apply evenRank_le_two_of_pRank_le_two
  intro p hp hp2
  have hrK : ∀ n : ℕ, (p : GaloisField 2 n) ≠ 0 := fun n => natCast_ne_zero_of_charTwo hp hp2
  rcases hfam with ⟨n, hn, h⟩ | ⟨m, hm, ⟨e⟩⟩
  swap
  · exact pRank_le_two_of_suzuki hm e hp hp2
  rcases h with h | h | h | h
  · obtain ⟨e⟩ := h
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact pRank_projSL_two_le hp hp2 (hrK n)
  · obtain ⟨e⟩ := h
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact pRank_projSU_three_le hn hp hp2
  · obtain ⟨e⟩ := h
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact pRank_projSL_three_le hn (GaloisField.card 2 n (by omega)) hp hp2
  · obtain ⟨e⟩ := h
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact pRank_projSp_two_le hp hp2 (hrK n)

end CFSG.RankThree.PartOne

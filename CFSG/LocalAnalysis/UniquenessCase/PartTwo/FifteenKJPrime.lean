module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeAbs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeLie

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem rJPrime153_holds : RJPrime153 := by
  intro W _ _ hW J R hJR hfaith
  rcases hJR with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨m, hm, h⟩
  · rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      exact s15k_jp_sl_two hW h hfaith
    · exact s15k_jp_sl_three_le h3 h
  · rcases Nat.lt_or_ge n 6 with h6 | h6
    · obtain ⟨k, hk⟩ := h.1
      obtain rfl : n = 4 := by omega
      exact s15k_jp_sp_four h
    · exact s15k_jp_sp_six_le h6 h
  · exact s15k_jp_orth_plus hn h
  · rcases Nat.lt_or_ge n 6 with h6 | h6
    · obtain ⟨k, hk⟩ := h.1
      obtain rfl : n = 4 := by omega
      exact s15k_jp_sym hW (by norm_num) (s15k_jp_orth_minus_four h) hfaith
    · exact s15k_jp_orth_minus h6 h
  · exact s15k_jp_sym hW hm h hfaith

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

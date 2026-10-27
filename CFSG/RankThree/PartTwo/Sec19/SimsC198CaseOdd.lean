module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Cases
import CFSG.RankThree.PartTwo.Sec19.SimsC198L3
import CFSG.RankThree.PartTwo.Sec19.SimsC198RankOdd

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

theorem caseHolds_two : CaseHolds Alt42Two := by
  intro X _ _ _ c L 𝒟 hD h
  obtain ⟨p, e, _, hp, he, -, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ := h
  · have h3 : ringChar (GaloisField p e) ≠ 3 := by
      rw [ringChar.eq (GaloisField p e) p]
      omega
    exact absurd hD ((NoLocalDatum.of_mulEquiv φ
      (noLocalDatum_projSL_three (GaloisField p e) h3)).noAutDatum c L 𝒟)
  · exact absurd hD ((NoLocalDatum.of_mulEquiv φ
      (noLocalDatum_projSU_three p e (by omega) he)).noAutDatum c L 𝒟)

theorem caseHolds_three :
    CaseHolds Alt42Three := by
  intro X _ _ hX c L 𝒟 hD h
  obtain ⟨hr, ⟨φ⟩⟩ := h
  exact (false_of_rankHyp_ree27 hX hr φ).elim

theorem caseHolds_four :
    CaseHolds Alt42Four := by
  intro X _ _ hX c L 𝒟 hD h
  obtain ⟨p, _, hp, ⟨q, hqp, hq, hG⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ := h
  · exact (false_of_rankHyp_G2_large hX (by omega) hq hG).elim
  · exact (false_of_rankHyp_PSp4 hX hp φ).elim
  · exact (false_of_rankHyp_PSL4 hX hp φ).elim
  · exact (false_of_rankHyp_PSU4 hX hp φ).elim

theorem caseHolds_nine :
    CaseHolds Alt42Nine := by
  intro X _ _ hX c L 𝒟 hD h
  rcases h with ⟨e, he, -, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · rcases Nat.lt_or_ge e 2 with h2 | h2
    · obtain rfl : e = 1 := by omega
      exact absurd hD ((NoLocalDatum.of_mulEquiv φ
        noLocalDatum_projSL_three_three).noAutDatum c L 𝒟)
    · exact (false_of_rankHyp_PSL3_three hX h2 φ).elim
  · rcases Nat.lt_or_ge e 2 with h2 | h2
    · obtain rfl : e = 1 := by omega
      exact absurd hD ((NoLocalDatum.of_mulEquiv φ
        noLocalDatum_projSU_three_three).noAutDatum c L 𝒟)
    · exact (false_of_rankHyp_PSU3_three hX h2 φ).elim
  · exact (false_of_rankHyp_G2_three hX φ).elim
  · exact (false_of_rankHyp_PSL4_three hX φ).elim
  · exact (false_of_rankHyp_PSU4_three hX φ).elim

end CFSG.RankThree.PartTwo.Sec19.SimsC198

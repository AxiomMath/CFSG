module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSzLowK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdBorelFamilies
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdBorelL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open KOB

theorem kOrdBorel_holds : KOrdBorel := by
  intro X _ _ m hm hX r hr hr3 hrm hrq S θ hθ hS
  have hr2 : r ≠ 2 := by omega
  have hrq1 : ¬ r ∣ 2 ^ m - 1 := fun h => hrq (h.trans (two_pow_sub_one_dvd m))
  have hr2m : ¬ r ∣ 2 * m := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
    · exact hrm h2
  have hr6m : ¬ r ∣ 6 * m := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h6 | h6
    · have h7 := Nat.le_of_dvd (by norm_num) h6
      interval_cases r <;> first | omega | (norm_num at hr) | (exact absurd h6 (by norm_num))
    · exact hrm h6
  rcases hX with hSz | hL2 | ⟨hq, hU⟩ | ⟨hq, hL⟩ | hSp4 | hO
  · exact kob_Sz hSz hr hr2 hrm hrq1 S hθ hS
  · exact kob_L2 hL2 hr hr2 hrm hrq1 S hθ hS
  · exact eq_one_of_bar hq
      (fun σ T hσ hT => kob_U3 hU (center_quotient_eq_bot hq) hr hr2 hr6m hrq T hσ hT) S hθ hS
  · exact eq_one_of_bar hq
      (fun σ T hσ hT => kob_L3 hL (center_quotient_eq_bot hq) hr hr2 hr6m hrq1 T hσ hT) S hθ hS
  · exact kob_Sp4 hSp4 hr hr2 hr2m hrq1 S hθ hS
  · exact kob_Omega hO (by omega) hr hr2 hr2m hrq S hθ hS

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

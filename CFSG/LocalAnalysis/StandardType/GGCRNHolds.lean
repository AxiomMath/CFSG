module

public import CFSG.LocalAnalysis.StandardType.GGCRNTransport
public import CFSG.LocalAnalysis.StandardType.GGCRNLin
public import CFSG.LocalAnalysis.StandardType.GGCRNLinNs
public import CFSG.LocalAnalysis.StandardType.GGCRNSympOrth
public import CFSG.LocalAnalysis.StandardType.GGCRNOrthNs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ExcRank

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggCRN_lift
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hdeg : ((lab.tag = .A ∨ lab.tag = .twA) ∧ 24 ≤ lab.rank + 1) ∨
      ((lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD) ∧ 24 ≤ 2 * lab.rank)) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R := by
  rcases three_dvd_two_pow_pred_or_succ lab.n with h3 | h3
  · rcases hdeg with ⟨ht | ht, hd⟩ | ⟨ht | ht | ht | ht, hd⟩
    · exact ggCRN_lift_A_split hlab ht hd h3
    · exact ggCRN_lift_twA_split hlab ht hd h3
    · exact ggCRN_lift_BC_split hlab (Or.inl ht) hd h3
    · exact ggCRN_lift_BC_split hlab (Or.inr ht) hd h3
    · exact ggCRN_lift_D_split hlab ht hd h3
    · exact ggCRN_lift_twD_split hlab ht hd h3
  · rcases hdeg with ⟨ht | ht, hd⟩ | ⟨ht | ht | ht | ht, hd⟩
    · exact ggCRN_lift_A_nonsplit hlab ht hd h3
    · exact ggCRN_lift_twA_nonsplit hlab ht hd h3
    · exact ggCRN_lift_BC_nonsplit hlab (Or.inl ht) hd h3
    · exact ggCRN_lift_BC_nonsplit hlab (Or.inr ht) hd h3
    · exact ggCRN_lift_D_nonsplit hlab ht hd h3
    · exact ggCRN_lift_twD_nonsplit hlab ht hd h3

theorem ggClassicalTwoLocalRankNine_of_lifts :
    GGClassicalTwoLocalRankNine := by
  intro H _ _ hP lab hlab hHlab hdeg
  exact ggCRN_twoLocalRank_of_lift (ggCRN_lift hlab hdeg) hHlab

end CFSG.StandardType

end

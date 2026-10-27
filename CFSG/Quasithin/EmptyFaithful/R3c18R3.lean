module

public import CFSG.Quasithin.EmptyFaithful.R3c18R2
public import CFSG.Quasithin.EmptyFaithful.R3c18F

public section

namespace CFSG.Quasithin

namespace R3c18

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def LieTwoRest3Family (S : Type) [Group S] : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f

@[expose] def QLiePRankRest3 : Prop := QLiePRankFam (fun S _ => LieTwoRest3Family S)

section Assembly

set_option linter.unusedSectionVars false


theorem qLiePRankRest2_of_rest3 (hcls : F4ReeClass) (hrk : F4ReeRank) (hr : QLiePRankRest3) :
    QLiePRankRest2 := by
  have h := qLiePRankFam_or hr (qLiePRankFam_f4 hcls hrk)
  refine qLiePRankFam_mono (fun S _ hS => ?_) h
  rcases hS with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem qLiePRank_of_rest3 (hG2 : G2PRankShape) (hSp4 : Sp4PRankShape) (hL3 : L3PRankShape)
    (hU3 : U3PRankShape) (hcls : F4ReeClass) (hrk : F4ReeRank) (hr : QLiePRankRest3) :
    QLiePRank :=
  qLiePRank_of_rest2 hG2 hSp4 hL3 hU3 (qLiePRankRest2_of_rest3 hcls hrk hr)

end Assembly

end R3c18

end CFSG.Quasithin

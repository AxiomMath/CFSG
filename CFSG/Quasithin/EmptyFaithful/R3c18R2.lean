module

public import CFSG.Quasithin.EmptyFaithful.R3c18B
public import CFSG.Quasithin.EmptyFaithful.R3c18C
public import CFSG.Quasithin.EmptyFaithful.R3c18E

public section

namespace CFSG.Quasithin

namespace R3c18

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def LieTwoRest2Family (S : Type) [Group S] : Prop :=
  (∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
  (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f)

@[expose] def QLiePRankRest2 : Prop := QLiePRankFam (fun S _ => LieTwoRest2Family S)

section Assembly

set_option linter.unusedSectionVars false


theorem qLiePRank_of_rest2 (hG2 : G2PRankShape) (hSp4 : Sp4PRankShape) (hL3 : L3PRankShape)
    (hU3 : U3PRankShape) (hr : QLiePRankRest2) : QLiePRank := by
  have h := qLiePRankFam_or hr
    (qLiePRankFam_or (qLiePRankFam_l3 hL3)
      (qLiePRankFam_or (qLiePRankFam_u3 hU3)
        (qLiePRankFam_or (qLiePRankFam_sp4 hSp4) (qLiePRankFam_g2 hG2))))
  refine qLiePRank_iff_fam.2 (qLiePRankFam_mono (fun S _ hS => ?_) h)
  rcases hS with h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)

end Assembly

end R3c18

end CFSG.Quasithin

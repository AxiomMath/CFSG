module

public import CFSG.LocalAnalysis.StandardType.GGExcKGInndiagCIE6Three
public import CFSG.LocalAnalysis.StandardType.GGExcKGInndiagCITwE6Three

public section

namespace CFSG.StandardType

theorem ggKGInndiagCI_holds
    : GGKGInndiagCI := by
  intro t n f ht hadm p hp hp2 hreg π hπ
  refine ⟨fun E hE hdiag => ?_, ?_⟩
  · rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ggKGInndiagCIa_untwisted (Or.inl rfl) n f hadm hp hp2 hreg hπ hE hdiag
    · by_cases hrow : p = 3 ∧ π = 1
      · obtain ⟨rfl, hπ1⟩ := hrow
        exact ggKGInndiagCIa_E6_three n f hadm hπ1 ((hπ.2.2.1 rfl).1 hπ1) hE hdiag
      · exact ggKGInndiagCIa_E6_twistedE6 (Or.inl rfl) n f hadm hp hp2 hreg hπ hrow hE hdiag
    · exact ggKGInndiagCIa_untwisted (Or.inr (Or.inl rfl)) n f hadm hp hp2 hreg hπ hE hdiag
    · exact ggKGInndiagCIa_untwisted (Or.inr (Or.inr rfl)) n f hadm hp hp2 hreg hπ hE hdiag
    · by_cases hrow : p = 3 ∧ π = 1
      · obtain ⟨rfl, hπ1⟩ := hrow
        exact ggKGInndiagCIa_twistedE6_three n f hadm hπ1 ((hπ.2.2.2 rfl).1 hπ1) hE hdiag
      · exact ggKGInndiagCIa_E6_twistedE6 (Or.inr rfl) n f hadm hp hp2 hreg hπ hrow hE hdiag
  · rintro (rfl | rfl) rfl hπ1 E E' hE hE' hdiag hdiag' hcE hcE'
    · exact ggKGInndiagCId_E6_three n f hadm hπ1 ((hπ.2.2.1 rfl).1 hπ1) hE hE' hdiag hdiag'
        hcE hcE'
    · exact ggKGInndiagCId_twistedE6_three n f hadm hπ1 ((hπ.2.2.2 rfl).1 hπ1) hE hE' hdiag
        hdiag' hcE hcE'

end CFSG.StandardType

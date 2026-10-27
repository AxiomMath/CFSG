module

public import CFSG.RepresentationTheory.SL2NatSum.Quadratic
public import CFSG.RepresentationTheory.SL2NatSum.EightCert
public import CFSG.RepresentationTheory.SL2NatSum.Assembly
public import CFSG.LocalAnalysis.WeakClosure81.TwelveInputs

public section

namespace CFSG.RepresentationTheory.SL2NatSum

theorem natSumL2Input_holds : CFSG.LocalAnalysis.WeakClosure81.NatSumL2Input := by
  intro n hn1 H _ _ hH W _ _ _ ρ hD
  refine natSum_of_quadratic (n := n) ?_ hH ρ hD
  intro K _ _ _ hK V _ _ _ ρK hfpf
  have hn : n = 2 ∨ n = 3 ∨ 4 ≤ n := by omega
  rcases hn with rfl | rfl | hn4
  · exact quadratic_of_ne_three hK (Or.inl rfl) ρK hfpf
  · exact quadratic_of_card_eight (by simpa using hK) ρK hfpf
  · exact quadratic_of_ne_three hK (Or.inr hn4) ρK hfpf

end CFSG.RepresentationTheory.SL2NatSum

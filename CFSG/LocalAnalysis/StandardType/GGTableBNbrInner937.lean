module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Exc
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937U63
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6

public section

namespace CFSG.StandardType

section Main

theorem ggTableBNbrInnerInputOn_round13Exc_of_937 (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hF4 : GGNbrKGF4ThreeAddSC) (hE : GGNbrKGExcPlusSCWeylIrred)
    (hTw : GGNbrKGTwE6ThreeSubSCWeylIrred) (hU : GGUnitDvd63NbrRankInput)
    (hRest : GGTableBNbrInnerInputOn GGTableBNbrInnerRound14ExcLabel) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound13ExcLabel := by
  have h := (((ggTableBNbrInnerInputOn_937F4 hL hPJ hF4).or
    (ggTableBNbrInnerInputOn_937ExcPlus hL hPJ hE)).or
    ((ggTableBNbrInnerInputOn_937TwE6 hL hPJ hTw).or (ggTableBNbrInnerInputOn_937U63 hU))).or hRest
  refine GGTableBNbrInnerInputOn.mono (fun p lab hlab => ?_) h
  by_cases hc : GGNbrInner937F4Label p lab ∨ GGNbrInner937ExcPlusLabel p lab ∨
      GGNbrInner937TwE6Label p lab ∨ GGUnitDvd63Label p lab
  · rcases hc with h1 | h2 | h3 | h4
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr (Or.inl h3))
    · exact Or.inl (Or.inr (Or.inr h4))
  · exact Or.inr ⟨hlab, hc⟩

end Main

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthPer
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGStdSubSmallInputOn.mono_of_split {S T : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubSmallInputOn T)
    (hST : ∀ p lab, LargeEvenSplit p lab → S p lab → T p lab) : GGStdSubSmallInputOn S :=
  fun G _ _ p B Bs x L D J hcfg hM hsm => h G p B Bs x L D J hcfg
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hST p lab hP.2.1 hP.1, hP.2⟩) hM) hsm

section Main


open SmallOrth in
theorem ggStdSubSmallInputOn_orth_of_inputs (h1 : PlusSplitInput) (h2 : PlusTwoInput)
    (h3 : MinusSplitInput) (h4 : MinusUnitInput) (h5 : TwDFourInput) :
    GGStdSubSmallInputOn GGStdSubSmallOrthLabel :=
  ((ggStdSubSmallInputOn_orthGood_of_inputs h1 h2 h3 h4).or
    (ggStdSubSmallInputOn_twDFour_of_input h5)).mono_of_split fun p lab hs h => by
      rcases orthLabel_cases h hs with h' | h' | h' | h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr (Or.inl h'))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h')))
      · exact Or.inr h'

open SmallOrth in
theorem ggStdSubSmallInputOn_of_not_orth (h1 : PlusSplitInput) (h2 : PlusTwoInput)
    (h3 : MinusSplitInput) (h4 : MinusUnitInput) (h5 : TwDFourInput)
    {T : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubSmallInputOn fun p lab => T p lab ∧ ¬ GGStdSubSmallOrthLabel p lab) :
    GGStdSubSmallInputOn T :=
  ((ggStdSubSmallInputOn_orth_of_inputs h1 h2 h3 h4 h5).or h).mono fun p lab hT => by
    by_cases hl : GGStdSubSmallOrthLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hT, hl⟩

end Main

end CFSG.StandardType

end

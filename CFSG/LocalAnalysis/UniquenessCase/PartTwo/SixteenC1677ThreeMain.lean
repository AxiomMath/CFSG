module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeS2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_8F_three_of_r16_3FE
    {D : Data G} (hstd : S168e3Std D)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (h163 : R16_3FE D) (h164 : R16_4 D) (h165 : R16_5 D)
    (h6 : ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V),
      S168e3Ctx D V₀ V L hV → Case163_6 D V₀ V hV L → False) : R16_8F D :=
  r16_8F_of_choice fun _ _ _ _ hS hne hc =>
    s168e3_choice_of_r16_3FE ⟨hstd, hS, hne, hc⟩ hSchur h163 h164 h165 h6

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

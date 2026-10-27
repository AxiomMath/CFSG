module

public import CFSG.LocalAnalysis.StandardType.GGResUnitaryKRankFiveLDefs
public import CFSG.LocalAnalysis.StandardType.GGResRankFiveFieldTwoL
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggResMultiNodeRestThreeKUnitaryQGeFourFieldTwoInput_holds :
    GGResMultiNodeRestThreeKUnitaryQGeFourFieldTwoInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hdata
  obtain ⟨⟨hDK, ⟨lab, hlab, hr5, hn2, hmark⟩, -⟩, hL⟩ := hdata
  have hU : GGInnerDiagOnLabel (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n ∧
      p ∣ 2 ^ lab.n + 1) p Bs K := by
    refine GGInnerDiagOnLabel.mono_label (S := fun _ lab' => lab' = lab) ?_ hmark
    intro lab' hlab'
    subst lab'
    exact ⟨hlab.1, hr5, hn2, hlab.2.2.2⟩
  exact (hH.not_exactThree_K_of_rankFive_fieldTwo_L hU hL hDK).elim

end CFSG.StandardType

end

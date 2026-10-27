module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
public import Certificates.Certificate899051
import CFSG.LocalAnalysis.StandardType.FF81.LocalSetup
import CFSG.LocalAnalysis.StandardType.FF81.ModelN
import CFSG.LocalAnalysis.StandardType.FF81.PropTwoDict
import CFSG.LocalAnalysis.StandardType.FF81.PropTwoMon
import CFSG.LocalAnalysis.StandardType.FF81.PropTwoLines
import CFSG.LocalAnalysis.StandardType.FF81.PropTwoOdd
import CFSG.LocalAnalysis.StandardType.GGFFProp2

@[expose] public section

namespace CFSG.StandardType.FF81

open CFSG.RankThree.PartTwo.Sec21.FF81.P51 (sig01_of_W)

theorem propTwo_holds : PropTwo := by
  intro G _ _ _ _ hchar n b L hA z hz _ hmeet
  have hS : GGFF.SettingCore b L z := hA.settingCore hz
  have h : GGFF.Setting b L z := ⟨hS, hmeet⟩
  have hN : GGFF.ModelN L z := modelN_of_model hA.n_cases hA.model hz
  obtain ⟨Γ, cv, hM, hcase⟩ := exists_bCoordModel_cases h hN hchar
  rcases hcase with ⟨hA', -⟩ | ⟨hB', hW, hcard⟩
  · exact Or.inl ⟨isMonomial_of_mA hM hA', conjLinesOfB_of_mA hS hM hA'⟩
  · refine Or.inr ⟨containsMonomial_of_sig01 hM (sig01_of_W hM.hyp hW), ?_,
      conjLinesOfB_of_mB hS hM hB', odd_card_cenS_of_mB h hN hchar hM hB'⟩
    rw [GGFF.card_ggAutomizer_top, hcard]

end CFSG.StandardType.FF81

end

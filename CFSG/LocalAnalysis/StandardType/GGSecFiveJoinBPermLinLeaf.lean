module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinBPermDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinNbrTableP
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinSU6
import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinB
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUCompat

public section

namespace CFSG.StandardType


theorem ggSecFiveJoinBPermLinInput_holds : GGSecFiveJoinBPermLinInput := by
  intro hX hTCJ hRig hTPn hA8 hraw
    hiso hFC _ _ _ hLB _ _ hTBF _ _ hMp hWI _ _ hKnown G _ _ p B Bs x L D J 𝒦 hR hT1 _ _ ι M e hP
    hBM _ t n f ψ hpres hG0 m eta hm4 e' hP' hEta hLA hLab
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hR
  have hB : B = Bs := by
    refine (ggSecFiveRoute_bstar_eq_of_split hR (ggSplitLie_of_rowSA hp ?_)).symm
    refine largeEvenMarking_mono (fun lab _ _ _ _ _ h => ?_) hLab
    obtain ⟨⟨htag, hrank, hdvd⟩, -⟩ := h
    exact ⟨Or.inl ⟨htag, by omega⟩, hdvd⟩
  rcases ggSecFiveBPermLinNbrInput_of_label hX hTCJ hRig hTPn hA8 hraw hiso hFC
      (ggSecFiveBPermLinNbrLabelInput_of_tableP hRig hTPn hA8 hraw hiso hMp hLB)
      (ggSecFiveBPermLinSU6Input_of_balance hLB) G p B Bs x L D J 𝒦 hR hT1 m e' hP' hm4 eta hEta
      hLA hG0 hB hLab with hc | hc | hc | ⟨a, K, i0, hc⟩
  · exact hR.compat_of_bPermLin_regularCell hRig hKnown hTBF hWI hP hBM ψ hpres hm4 eta
      (Or.inl hc)
  · exact hR.compat_of_bPermLin_regularCell hRig hKnown hTBF hWI hP hBM ψ hpres hm4 eta
      (Or.inr (Or.inl hc))
  · exact hR.compat_of_bPermLin_regularCell hRig hKnown hTBF hWI hP hBM ψ hpres hm4 eta
      (Or.inr (Or.inr hc))
  · exact hR.compat_of_suCell hMp hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hB eta hEta hLA hc hG0

end CFSG.StandardType

end

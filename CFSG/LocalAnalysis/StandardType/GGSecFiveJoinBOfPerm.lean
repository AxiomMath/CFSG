module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinBCellDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinBPermDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinBGuarded
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinB
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPosition
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal


theorem ggSecFiveJoinBOfKnownInput_of_perm (hUni : GGSecFiveJoinBPermUniInput)
    (hLin : GGSecFiveJoinBPermLinInput) : GGSecFiveJoinBOfKnownInput := by
  intro hX hTCJ hRig hTPn hA8 hraw hiso hFC hT hLift hI3 hLB hPJ hTE6R hTBF hRoot hCP hMp hWI
    hDXE hU62 hKnown G _ _ p B Bs x L D J 𝒦 hcfg hT1 hARow hQ ι M e hP hB hSix t n f ψ hpres hG0
  have hB0 := hB
  obtain ⟨m, σ, hm, rfl⟩ := hB
  have hPB := GGCoxeterPres.of_reindex_B (A := ggAutomizerJoin L Bs 𝒦) hm hP
  obtain ⟨hm4, eta, i0, hjoin, hLpos⟩ :=
    bOriginalPositionTheoryInput_holds hTBF hWI hX hTCJ hRig G p B Bs x L D J 𝒦 hcfg m hm _ hPB
  rcases hLpos with hLb | hLd | hLA
  ·
    have hlabel := ggSecFiveBCoordBLabelInput_of_res hT hLift ggSecFiveBCoordBResInput_holds
      G p B Bs x L D J 𝒦 hcfg m hm4 eta i0 hLb
    exact ggSecFiveCompatJoinB_of_guarded hKnown hcfg hTBF hWI hP hB0 ψ hpres (Or.inl rfl)
      (largeEvenMarking_mono (fun lab _ _ _ _ _ h => guardedLargeEvenLabel_of_coordB hm4 h.1)
        hlabel)
  ·
    exact (hDXE G p B Bs x L D J 𝒦 hcfg m eta i0 hm4 hjoin hLd).elim
  ·
    rcases (ggSecFiveBPermLabelInput_holds G p B Bs x L D J 𝒦 hcfg m hm4 eta hLA).elim_or with
      hLab | hLab
    · exact hLin hX hTCJ hRig hTPn hA8 hraw hiso hFC hT hLift hI3 hLB hPJ hTE6R hTBF hRoot hCP
        hMp hWI hDXE hU62 hKnown G p B Bs x L D J 𝒦 hcfg hT1 hARow hQ ι _ e hP hB0 hSix t n f ψ
        hpres hG0 m eta hm4 _ hPB hjoin hLA hLab
    · exact hUni hX hTCJ hRig hTPn hA8 hraw hiso hFC hT hLift hI3 hLB hPJ hTE6R hTBF hRoot hCP
        hMp hWI hDXE hU62 hKnown G p B Bs x L D J 𝒦 hcfg hT1 hARow hQ ι _ e hP hB0 hSix t n f ψ
        hpres hG0 m eta hm4 _ hPB hjoin hLA hLab

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinBPermDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinBPermUniNbr

public section

namespace CFSG.StandardType


theorem ggSecFiveJoinBPermUniInput_holds : GGSecFiveJoinBPermUniInput := by
  intro hX hTCJ hRig hTPn hA8 hraw hiso hFC
    hT hLift hI3 hLB hPJ hTE6R hTBF hRoot hCP _ hWI _ hU62 hKnown G _ _ p B Bs x L D J 𝒦 hcfg _ _ _
    _ _ _ hP hB _ _ _ _ ψ hpres _ _ eta hm _ hPm hJoin hAut hU
  obtain ⟨y, K, -, hnb, -, hmark⟩ := hcfg.exists_guarded_nbr_of_bPermUni hTBF hWI hX hTCJ hRig
    hTPn hA8 hraw hiso hFC hT hLift hI3 hLB hPJ hTE6R hRoot hCP hU62 hPm hm eta hJoin hAut hU
  exact ggSecFiveCompatJoinB_of_guarded hKnown hcfg hTBF hWI hP hB ψ hpres (Or.inr ⟨y, hnb⟩) hmark

end CFSG.StandardType

end

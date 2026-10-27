module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSmallDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaMain

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveNSEnnolaSmallInput_holds

    : GGSecFiveNSEnnolaSmallInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hregion hns ι M e hpres hA hrow
  obtain ⟨n, e', -, hM⟩ := hA
  exact ggSecFiveNSEnnola_absurd_L hcfg hpres hM hrow

end CFSG.StandardType

end

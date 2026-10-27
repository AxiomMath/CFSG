module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSExclDDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaMain
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaDFork
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveNSEnnolaDInput_holds :
    GGSecFiveNSEnnolaDInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ ι M e hpres hD i j hij hMij hno hrow
  exact ggSecFiveNSEnnola_core_of_noReflFork hcfg hpres
    (fun i j hij => GGIsWeylMatrixAD.le_three (Or.inr hD) i j hij) (Or.inl rfl)
    (ggL_noReflFork_typeD hcfg hpres hD hij hMij hno) (fun hp3 hLab hN => by
      subst hp3
      exact ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg.1.1 hLab hN) hrow

end CFSG.StandardType

end

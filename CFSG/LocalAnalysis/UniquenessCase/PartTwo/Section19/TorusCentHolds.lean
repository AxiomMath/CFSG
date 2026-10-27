module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFiveTrichotomy
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusSp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusProd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

theorem k_19_25_torusCent_holds : K_19_25_torusCent :=
  fun _ _ _ _ hn hodd _ hT _ hxT _ =>
    ⟨fun hX => k_19_25_torusCent_sp4 hn hodd hX hT hxT,
      fun S₁ S₂ h₁ h₂ hinf hsup hS => k_19_25_torusCent_prod hT hxT S₁ S₂ h₁ h₂ hinf hsup hS⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

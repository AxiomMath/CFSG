module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyEightCorrected
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusAutomizerSp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusAutomizerProd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

theorem k_19_28_torusAutomizer_holds : K_19_28_torusAutomizer :=
  fun _ _ _ _ hn hodd hX _ hT σ hσ hσT ht₀ =>
    hX.elim (fun h => k_19_28_torusAutomizer_sp4 hn hodd h hT σ hσ hσT ht₀)
      (fun h => k_19_28_torusAutomizer_prod hn hodd h hT σ hσ hσT ht₀)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

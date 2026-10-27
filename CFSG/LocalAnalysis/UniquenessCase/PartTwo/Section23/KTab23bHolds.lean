module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSp4Natural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSU4Final
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega6Minus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega6Plus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8MinusLeviFinal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem kTab23b_of_naturalLines
    (hsurjSplit : ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 ^ m → m ≠ 1 →
      ∃ f : ↥(Hinf (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.rankOneParabolic K 3 0)) →*
          Matrix.SpecialLinearGroup (Fin 2) K, Function.Surjective f ∧ IsPGroup 2 f.ker)
 :
    KTab23b := by
  intro W _ _ H n hnat hperf
  exact fun S Tstar hTnorm hT2 hST =>
    ⟨fun hline => kTab23b_L2_line_uncond W H n hnat hperf hline S Tstar hTnorm hT2 hST,
     fun hline => kTab23b_OmegaMinus_line_uncond W H n hnat hperf hline S Tstar hTnorm hT2 hST,
     fun hline => kTab23b_OmegaPlus_line_uncond W H n hnat hperf ⟨hline.1, hline.2.1⟩ S Tstar hTnorm hT2 hST hline.2.2,
     fun hline => kTab23b_Sp4_line_uncond_final W H n hnat hperf hline S Tstar hTnorm hT2 hST,
     fun hline => kTab23b_SL3_line_uncond_final W H n hnat hperf hline S Tstar hTnorm hT2 hST,
     fun hprem => kTab23b_SU4_line_uncond_final W H n hnat hperf S Tstar hTnorm hT2 hST hprem,
     fun hline => kTab23b_OmegaMinus6_line_of_natural W H n hnat hperf hline
       omegaMinus6NaturalLine_holds
       S Tstar hTnorm hT2 hST,
     fun hline => kTab23b_SL4_line_of_naturalModel W H n hnat hperf hline sl4NaturalModel_holds
       S Tstar hTnorm hT2 hST,
     fun hline => kTab23b_OmegaPlus6_line_of_natural W H n hnat hperf hline
       (omegaPlus6Natural_holds_cond hsurjSplit)
       S Tstar hTnorm hT2 hST,
     fun hline => kTab23b_Sp6_line_uncond W H n hnat hperf hline S Tstar hTnorm hT2 hST,
     fun hline => kTab23b_OmegaMinus8_line_of_natural W H n hnat hperf hline omegaMinus8Natural_holds
       S Tstar hTnorm hT2 hST⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

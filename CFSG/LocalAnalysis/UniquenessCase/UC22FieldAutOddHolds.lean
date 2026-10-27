module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddLinear
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddSymplectic
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddSubfield

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22


theorem kFieldAutOdd_holds : KFieldAutOdd := by
  intro X _ _ _ t n p f r hp hp2 hadm hX hA1 hRee hr hr5 hrg θ hθ hout
  cases t with
  | PSL => exact fieldAutOdd_psl hp hadm hX hA1 hr hr5 hrg θ hθ hout
  | PSp => exact fieldAutOdd_psp hp hp2 hX hr hr5 θ hθ hout
  | PSU | POmegaOdd | POmegaPlus | POmegaMinus =>
    obtain ⟨hrf, Y, hY, hmodel⟩ := fieldAutOdd_remainingClassical_subfield
      (by simp) hp hp2 hadm hX hr hr5 hrg θ hθ hout
    exact ⟨hrf, fieldAutOdd_of_classical_subfield (by decide) hp2 hA1 θ hY hmodel⟩
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 =>
    exact fieldAutOdd_exceptional (by decide) hp hp2 hadm hX hr hr5 θ hθ hout
  | twistedG2 => exact (hRee rfl).elim
  | twistedB2 | twistedF4 | Tits => exact (hp2 hadm.2.2.2.1).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22

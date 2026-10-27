module

public import Certificates.Kernel.C260411.Data
public import Certificates.Kernel.C260411.Pins
public import Certificates.Data.SmithB45J2Nor

public section

namespace CFSG.KD.C260411

open CFSG.KC.B45M12 CFSG.KC.B45J2 CFSG.Quasithin.J2Mod

theorem nor6 :
    norL 6 c6TermWords c6TermCoeffs c6Q c6Qi c6R c6Si c6Ti c6W c6Spin c6Dual A6 B6 = true := by
  decide +kernel

theorem nor14 :
    norL 14 c14TermWords c14TermCoeffs c14Q c14Qi c14R c14Si c14Ti c14W c14Spin c14Dual
      T14A T14B = true := by
  decide +kernel

theorem nor36 :
    norL 36 c36TermWords c36TermCoeffs c36Q c36Qi c36R c36Si c36Ti c36W c36Spin c36Dual
      (kronF4 6 6 A6 (frobF4 A6)) (kronF4 6 6 B6 (frobF4 B6)) = true := by
  decide +kernel

theorem trace6_14 :
    traceK 6 (wordF4 6 A6 B6 tw6) 2 = true ∧ traceK 14 (wordF4 14 T14A T14B tw14) 3 = true := by
  decide +kernel

end CFSG.KD.C260411

end

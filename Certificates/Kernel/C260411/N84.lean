module

public import Certificates.Kernel.C260411.Data
public import Certificates.Kernel.C260411.Pins
public import Certificates.Data.SmithB45J2Nor

public section

namespace CFSG.KD.C260411

open CFSG.KC.B45M12 CFSG.KC.B45J2 CFSG.Quasithin.J2Mod

theorem nor84 :
    norL 84 c84TermWords c84TermCoeffs c84Q c84Qi c84R c84Si c84Ti c84W c84Spin c84Dual
      (kronF4 6 14 A6 (frobF4 T14A)) (kronF4 6 14 B6 (frobF4 T14B)) = true := by
  decide +kernel

end CFSG.KD.C260411

end

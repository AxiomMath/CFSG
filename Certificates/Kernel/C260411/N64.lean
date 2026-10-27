module

public import Certificates.Kernel.C260411.Pins
public import Certificates.Data.SmithB45J2Nor
public import Certificates.Data.Kernel.B45J2.Defs

public section

namespace CFSG.KD.C260411

open CFSG.KC.B45M12 CFSG.KC.B45J2 CFSG.Quasithin.J2Mod

theorem nor64 :
    norL 64 c64TermWords c64TermCoeffs c64Q c64Qi c64R c64Si c64Ti c64W c64Spin c64Dual
      T64A T64B = true := by
  decide +kernel

theorem trace64 : traceK 64 (wordF4 64 T64A T64B tw64) 3 = true := by
  decide +kernel

end CFSG.KD.C260411

end

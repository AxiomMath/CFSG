module

public import Certificates.Kernel.C260411.Pins
public import Certificates.Data.SmithB45J2Nor
public import Certificates.Data.Kernel.B45J2.Defs

public section

namespace CFSG.KD.C260411

open CFSG.KC.B45M12 CFSG.KC.B45J2 CFSG.Quasithin.J2Mod

theorem nor160 :
    norL 160 c160TermWords c160TermCoeffs c160Q c160Qi c160R c160Si c160Ti c160W c160Spin
      c160Dual T160A T160B = true := by
  decide +kernel

end CFSG.KD.C260411

end

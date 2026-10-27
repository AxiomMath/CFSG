module

public import Certificates.Data.SmithB45MatM22Nor
public import Certificates.Kernel.C260402.Pins
public import Certificates.Data.Kernel.B45M12.Mask

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat.M22

theorem nor34 : norF2 34 c34TermWords c34TermCoeffs c34QRows c34QiRows c34RRows c34SiRows
    c34TiRows c34W c34Spin c34Dual T34A T34B = true := by
  decide +kernel

end CFSG.KD.C260402

end

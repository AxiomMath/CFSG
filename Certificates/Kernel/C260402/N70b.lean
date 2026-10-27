module

public import Certificates.Data.SmithB45MatM22Nor
public import Certificates.Kernel.C260402.Pins
public import Certificates.Data.Kernel.B45M12.Four

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat.M22

theorem nor70b : norF4 70 c70bTermWords c70bTermCoeffs c70bQRows c70bQiRows c70bRRows c70bSiRows
    c70bTiRows c70bW c70bSpin c70bDual (frobF4 T70aA) (frobF4 T70aB) = true := by
  decide +kernel

end CFSG.KD.C260402

end

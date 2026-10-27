module

public import Certificates.Data.SmithB45MatM22Nor
public import Certificates.Kernel.C260402.Pins
public import Certificates.Data.Kernel.B45M12.Four

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat.M22

theorem nor70a : norF4 70 c70aTermWords c70aTermCoeffs c70aQRows c70aQiRows c70aRRows c70aSiRows
    c70aTiRows c70aW c70aSpin c70aDual T70aA T70aB = true := by
  decide +kernel

end CFSG.KD.C260402

end

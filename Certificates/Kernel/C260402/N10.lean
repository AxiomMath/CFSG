module

public import Certificates.Data.SmithB45MatM22Nor
public import Certificates.Kernel.C260402.Pins
public import Certificates.Data.Kernel.B45M12.Mask

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat.M22

theorem nor10a : norF2 10 c10aTermWords c10aTermCoeffs c10aQRows c10aQiRows c10aRRows c10aSiRows
    c10aTiRows c10aW c10aSpin c10aDual C10aA C10aB = true := by
  decide +kernel

theorem nor10b : norF2 10 c10bTermWords c10bTermCoeffs c10bQRows c10bQiRows c10bRRows c10bSiRows
    c10bTiRows c10bW c10bSpin c10bDual C10bA C10bB = true := by
  decide +kernel

end CFSG.KD.C260402

end

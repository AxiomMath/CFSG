module

public import Certificates.Data.SmithB45MatM22Nor
public import Certificates.Kernel.C260402.Pins
public import Certificates.Data.Kernel.B45M12.Mask

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat.M22

theorem nor98 : norF2 98 c98TermWords c98TermCoeffs c98QRows c98QiRows c98RRows c98SiRows
    c98TiRows c98W c98Spin c98Dual T98A T98B = true := by
  decide +kernel

end CFSG.KD.C260402

end

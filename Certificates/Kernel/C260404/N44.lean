module

public import Certificates.Data.Kernel.B45M12.Mask
public import Certificates.Data.SmithB45MatM12Nor
public import Certificates.Kernel.C260404.Pins

public section

namespace CFSG.KD.C260404

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12

theorem nor44 : norF2 44 c44TermWords c44TermCoeffs c44QRows c44QiRows c44RRows c44SiRows
    c44TiRows c44W c44Spin c44Dual T44A T44B = true := by
  decide +kernel

end CFSG.KD.C260404

end

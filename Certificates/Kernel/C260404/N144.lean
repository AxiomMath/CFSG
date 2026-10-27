module

public import Certificates.Data.Kernel.B45M12.Mask
public import Certificates.Data.SmithB45MatM12Nor
public import Certificates.Kernel.C260404.Pins

public section

namespace CFSG.KD.C260404

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12

theorem nor144 : norF2 144 c144TermWords c144TermCoeffs c144QRows c144QiRows c144RRows c144SiRows
    c144TiRows c144W c144Spin c144Dual T144A T144B = true := by
  decide +kernel

end CFSG.KD.C260404

end

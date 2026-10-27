module

public import Certificates.Data.Kernel.B45M12.Mask
public import Certificates.Data.SmithB45MatM12Nor

public section

namespace CFSG.KD.C260404

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12

theorem nor10 : norF2 10 c10TermWords c10TermCoeffs c10QRows c10QiRows c10RRows c10SiRows
    c10TiRows c10W c10Spin c10Dual (cols10 arrA) (cols10 arrB) = true := by
  decide +kernel

end CFSG.KD.C260404

end

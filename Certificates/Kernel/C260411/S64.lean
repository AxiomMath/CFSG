module

public import Certificates.Kernel.C260411.Data
public import Certificates.Kernel.C260411.Pins

public section

namespace CFSG.KD.C260411

open CFSG.KC.B45M12 CFSG.KC.B45J2

theorem sub64 :
    subKF4 84 64 B64c P64c [(kronF4 6 14 A6 T14A, T64A), (kronF4 6 14 B6 T14B, T64B)] = true := by
  decide +kernel

end CFSG.KD.C260411

end

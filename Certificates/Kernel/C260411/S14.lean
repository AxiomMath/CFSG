module

public import Certificates.Kernel.C260411.Data
public import Certificates.Kernel.C260411.Pins

public section

namespace CFSG.KD.C260411

open CFSG.KC.B45M12 CFSG.KC.B45J2

theorem sub14 :
    subKF4 36 14 B14c P14c [(kronF4 6 6 A6 A6, T14A), (kronF4 6 6 B6 B6, T14B)] = true := by
  decide +kernel

end CFSG.KD.C260411

end

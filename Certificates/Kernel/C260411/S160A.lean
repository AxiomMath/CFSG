module

public import Certificates.Kernel.C260411.Data
public import Certificates.Kernel.C260411.Pins

public section

namespace CFSG.KD.C260411

open CFSG.KC.B45M12 CFSG.KC.B45J2

theorem sub160A :
    subKF4 196 160 B160c P160c [(kronF4 14 14 T14A (frobF4 T14A), T160A)] = true := by
  decide +kernel

end CFSG.KD.C260411

end

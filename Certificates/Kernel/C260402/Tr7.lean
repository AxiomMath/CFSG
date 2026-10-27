module

public import Certificates.Kernel.C260402.Pins
public import Certificates.Data.Kernel.B45M12.Four

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12

theorem trace10a : traceK 10 (ofF2 C10aG7) 0 = true := by
  decide +kernel

theorem trace10b : traceK 10 (ofF2 C10bG7) 1 = true := by
  decide +kernel

end CFSG.KD.C260402

end

module

public import Certificates.Kernel.C21205.SylowData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.C21205S

open CFSG.KC.C21205

theorem sylowK_ok : sylowK PQ i0 ng G R PD CJ = true := by quickRfl

end CFSG.KD.C21205S

end

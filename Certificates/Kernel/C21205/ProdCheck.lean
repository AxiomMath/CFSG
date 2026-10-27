module

public import Certificates.Data.Kernel.C21205.Prod
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.C21205C

open CFSG.KC.C21205 CFSG.KC.Ord

theorem ch21205p2 : prodK 2 = true := by quickRfl

theorem ch21205p3 : prodK 3 = true := by quickRfl

end CFSG.KD.C21205C

end

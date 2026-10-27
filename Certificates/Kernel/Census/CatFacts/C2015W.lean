
module

public import Certificates.Data.Kernel.Census.CatFacts.C2015Defs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.CatFacts

theorem cnt2015K : cnt2015 = (45, 45, 1440, 720) := by
  decide +kernel

theorem oddN2015K : oddNW = true := by
  decide +kernel

end CFSG.Certificates.Kernel.CatFacts

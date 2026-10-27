
module

public import Certificates.Data.Kernel.Census.CatFacts.C2015Scan

public section

set_option maxHeartbeats 0

namespace CFSG.Certificates.Kernel.CatFacts

theorem fpf2015K : fpf2015 = true := by
  decide +kernel

end CFSG.Certificates.Kernel.CatFacts

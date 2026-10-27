module

public import Certificates.Data.Kernel.CertF8.Gen64

public section

namespace Certificates.Kernel.CertF8

open CFSG.KC.CertF8.G64

theorem ch17201c0 : genCheckClassQ 0 = true := by
  decide +kernel

theorem ch17201c1 : genCheckClassQ 1 = true := by
  decide +kernel

end Certificates.Kernel.CertF8

end

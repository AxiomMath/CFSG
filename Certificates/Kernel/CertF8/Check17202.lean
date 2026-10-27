module

public import Certificates.Data.Kernel.CertF8.Gen64

public section

namespace Certificates.Kernel.CertF8

open CFSG.KC.CertF8.G64

theorem ch17202c2 : genCheckClassQ 2 = true := by
  decide +kernel

theorem ch17202c3 : genCheckClassQ 3 = true := by
  decide +kernel

end Certificates.Kernel.CertF8

end

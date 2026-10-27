module

public import Certificates.Data.Kernel.Cert690.SqPass

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPass

open CFSG.KC.C690

theorem passPos : passL (idxT [(0, 0), (1, 1)]) 2 3 [0, 1, 0] 0 0 = true := by decide +kernel

theorem passNegFirst : passL (idxT [(0, 0), (1, 2)]) 2 3 [0, 1, 0] 0 0 = false := by
  decide +kernel

theorem passNegMask : passL (idxT [(0, 0), (1, 1)]) 2 1 [0, 1, 0] 0 0 = false := by
  decide +kernel

theorem passNegRange : passL (idxT [(0, 0), (1, 1)]) 1 3 [0, 1, 0] 0 0 = false := by
  decide +kernel

theorem passGoNegLen : passGo (idxT []) (idxT []) 0 0 0 [1] [] = false := by decide +kernel


end CertificateChecks.KernelC690.SqPass

end

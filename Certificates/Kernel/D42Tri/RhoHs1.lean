module

public import Certificates.Kernel.D42Tri.RhoRec
public import CFSG.Certificates.Kernel.Common.EachTrue
public import Certificates.Data.Kernel.Spor.MulHF

set_option maxRecDepth 400000

public section

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH CertificateChecks.KernelD42Tri in
#kc_each CertificateChecks.KernelD42Tri ch17628hsF_
  (fun s => slK RC.cnt (hsortPtKF 360 9 (mask 9) RC.cnt RC.T RC.HS RC.HSI) (1200 * s) 1200) 6 12

end

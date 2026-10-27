module

public import Certificates.Kernel.Cert690.CensSMB
public import Certificates.Kernel.Cert690.CensSMData0
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.C690S CertificateChecks.KernelC690.CensSM0 in
#kc_each CertificateChecks.KernelC690.CensSM0 ok
  (checkAt CertificateChecks.KernelC690.CensSM.base lo ginv wg cpar T orb reps ranks recs cls)
  0 126

end

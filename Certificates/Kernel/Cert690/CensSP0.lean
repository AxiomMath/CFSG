module

public import Certificates.Kernel.Cert690.CensSPB
public import Certificates.Kernel.Cert690.CensSPData0
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

open CFSG.KC.C690S CertificateChecks.KernelC690.CensSP0 in
#kc_each CertificateChecks.KernelC690.CensSP0 ok
  (checkAt CertificateChecks.KernelC690.CensSP.base lo ginv wg cpar T orb reps ranks recs cls)
  0 156

end

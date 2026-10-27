module

public import Certificates.Data.Kernel.SporSch.Co1MatW
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.Co1I301.Gen810305
public meta import Certificates.Kernel.SporSch.Co1.GenBfs
meta import Certificates.Kernel.Co1I301.In810305
public import CFSG.Assembly.Defs
public import Certificates.Kernel.SporSch.Co1.GenBfs

public section

set_option maxRecDepth 400000

#kc_eval CertificateChecks.KernelCo1I301 KI CertificateChecks.KernelCo1I301.step810305
#kss_co1gt CertificateChecks.KernelCo1I301.R0T CertificateChecks.KernelCo1I301.r0Arr 128
#kss_co1cts CertificateChecks.KernelCo1I301.DT CertificateChecks.KernelCo1I301.dGs
  CertificateChecks.KernelCo1I301.dGis CertificateChecks.KernelCo1I301.dRs
  CertificateChecks.KernelCo1I301.dCs

end

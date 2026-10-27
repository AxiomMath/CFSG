module

public import Certificates.Kernel.AE6Q8.Chain
public meta import Certificates.Kernel.AE6Q8.Chain
public import Certificates.Data.Kernel.SporSch.ClsAll
public meta import Certificates.Kernel.SporSch.GenClsAll
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.GenClsAll

public section

set_option maxRecDepth 400000

#kss_ptcntn CertificateChecks.KernelAE6Q8.SN CertificateChecks.KernelAE6Q8.SC 360 9
  CertificateChecks.KernelAE6Q8.strongS CertificateChecks.KernelAE6Q8.baseS 2

#kss_clsall CertificateChecks.KernelAE6Q8.SK CertificateChecks.KernelAE6Q8.SC 360 9
  CertificateChecks.KernelAE6Q8.strongS CertificateChecks.KernelAE6Q8.baseS 4 2
  CertificateChecks.KernelAE6Q8.zArr

end

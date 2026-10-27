module

public meta import Certificates.Kernel.SporSch.Co1.GenBfs
meta import Certificates.Kernel.Co1B.In2044
public import Certificates.Kernel.SporSch.Co1.GenBfs
import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

#kss_co1gt CertificateChecks.KernelCo1B.C2044.QT CertificateChecks.KernelCo1B.C2044.qArr 512

#kss_co1cts CertificateChecks.KernelCo1B.C2044.CT CertificateChecks.KernelCo1B.C2044.cG
  CertificateChecks.KernelCo1B.C2044.cGi CertificateChecks.KernelCo1B.C2044.cR
  CertificateChecks.KernelCo1B.C2044.cS

end

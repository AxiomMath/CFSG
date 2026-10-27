module

public meta import Certificates.Kernel.SporSch.Co1.GenBfs
meta import Certificates.Kernel.Co1B.In2047
public import Certificates.Kernel.SporSch.Co1.GenBfs
import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

#kss_co1gt CertificateChecks.KernelCo1B.C2047.QT CertificateChecks.KernelCo1B.C2047.qArr 2048

#kss_co1cts CertificateChecks.KernelCo1B.C2047.CT CertificateChecks.KernelCo1B.C2047.cG
  CertificateChecks.KernelCo1B.C2047.cGi CertificateChecks.KernelCo1B.C2047.cR
  CertificateChecks.KernelCo1B.C2047.cS

end

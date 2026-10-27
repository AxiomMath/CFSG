module

public meta import Certificates.Kernel.SporSch.Co1.GenDag
meta import Certificates.Kernel.Co1B.In2047
public import Certificates.Kernel.SporSch.Co1.GenDag
import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

#kss_co1dag CertificateChecks.KernelCo1B.C2047.D1 CertificateChecks.KernelCo1B.C2047.dag₁

#kss_co1dag CertificateChecks.KernelCo1B.C2047.D2 CertificateChecks.KernelCo1B.C2047.dag₂

end

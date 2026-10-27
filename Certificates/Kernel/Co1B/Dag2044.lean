module

public meta import Certificates.Kernel.SporSch.Co1.GenDag
meta import Certificates.Kernel.Co1B.In2044
public import Certificates.Kernel.SporSch.Co1.GenDag
import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

#kss_co1dag CertificateChecks.KernelCo1B.C2044.D1 CertificateChecks.KernelCo1B.C2044.dag₁

#kss_co1dag CertificateChecks.KernelCo1B.C2044.D2 CertificateChecks.KernelCo1B.C2044.dag₂

end

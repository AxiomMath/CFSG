module

public meta import Certificates.Kernel.SporSch.Co1.GenDag
meta import Certificates.Kernel.Co1B.In24512
public import Certificates.Kernel.SporSch.Co1.GenDag
import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

#kss_co1dag CertificateChecks.KernelCo1B.H24512.PC CertificateChecks.KernelCo1B.H24512.dPC
#kss_co1dag CertificateChecks.KernelCo1B.H24512.UC CertificateChecks.KernelCo1B.H24512.dUC
#kss_co1dag CertificateChecks.KernelCo1B.H24512.FC CertificateChecks.KernelCo1B.H24512.dFC
#kss_co1dag CertificateChecks.KernelCo1B.H24512.QC CertificateChecks.KernelCo1B.H24512.dQC

end

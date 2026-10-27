module

public import Certificates.Data.Kernel.SporSch.Co1MatW
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.Co1Planes.Gen
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public import CFSG.Assembly.Defs
public import Certificates.Kernel.SporSch.Co1.GenDag

public section

set_option maxRecDepth 400000 in
#kc_eval CertificateChecks.KernelCo1Planes CP CertificateChecks.KernelCo1Planes.Gen.planesStep

#kss_co1dag CertificateChecks.KernelCo1Planes.DA CertificateChecks.KernelCo1Planes.Gen.dagA

#kss_co1dag CertificateChecks.KernelCo1Planes.DC CertificateChecks.KernelCo1Planes.Gen.dagC

#kss_co1dag CertificateChecks.KernelCo1Planes.DB CertificateChecks.KernelCo1Planes.Gen.dagB

end

module

public import Certificates.Data.Kernel.SporSch.Co1MatW
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.Co1B.Gen431007
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.SporSch.Co1.GenBfs
meta import Certificates.Kernel.Co1B.In431007
public import CFSG.Assembly.Defs
public import Certificates.Kernel.SporSch.Co1.GenBfs
public import Certificates.Kernel.SporSch.Co1.GenDag

public section

set_option maxRecDepth 400000

#kc_eval CertificateChecks.KernelCo1B.Bound431007 KF CertificateChecks.KernelCo1B.Bound431007.stepF
#kss_co1dag CertificateChecks.KernelCo1B.Bound431007.DF CertificateChecks.KernelCo1B.Bound431007.kDag5
#kss_co1gt CertificateChecks.KernelCo1B.Bound431007.FAT CertificateChecks.KernelCo1B.Bound431007.fAArr 100
#kss_co1gt CertificateChecks.KernelCo1B.Bound431007.EAT CertificateChecks.KernelCo1B.Bound431007.eAArr 400
#kss_co1gt CertificateChecks.KernelCo1B.Bound431007.FBT CertificateChecks.KernelCo1B.Bound431007.fBArr 100
#kss_co1gt CertificateChecks.KernelCo1B.Bound431007.EBT CertificateChecks.KernelCo1B.Bound431007.eBArr 400

end

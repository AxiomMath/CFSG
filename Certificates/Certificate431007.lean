module

public import Certificates.Data.Co1FiveRank
public meta import Certificates.Data.Co1FiveRank
import Certificates.Kernel.Co1B.C431007

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.GLTheoremA.H1017.Co1FiveNative in
theorem certificate431007 : co1FiveCheck () = true := KernelCo1B.Bound431007.c431007

end Certificates

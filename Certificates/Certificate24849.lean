module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataOmegaDefs
import Certificates.Kernel.M24QdQ.Check
public import Certificates.Certificate11003

public section

namespace Certificates

open CertificateChecks

theorem certificate24849 : CFSG.EvenSporadicStandard.M24Std.QdQData := KernelM24QdQ.qdQData

end Certificates

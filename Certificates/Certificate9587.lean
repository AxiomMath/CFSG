module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Check
import Certificates.Kernel.D42.Checks
import CFSG.Certificates.Kernel.D42KSound

public section

namespace Certificates

open CertificateChecks

theorem certificate9587 : CFSG.AGLEmbedding.ChevOuter.D42Check :=
  CFSG.KC.D42K.d42Check_of KernelD42.checkK KernelD42.slpAll

end Certificates

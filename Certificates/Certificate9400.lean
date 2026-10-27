module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRankData
import Certificates.Kernel.Fi22Guest.Final

public section

namespace Certificates

open CFSG.AGLEmbedding.KFactProofs.Fi22Guest in
theorem certificate9400 : fi22GuestCheck = true :=
  CertificateChecks.KernelFi22Guest.guest_check

end Certificates

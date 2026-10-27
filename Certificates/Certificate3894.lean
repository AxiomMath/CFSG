module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
import Certificates.Kernel.OmegaEight.SB3884K1

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3884 CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3894 : (∃ gs L, l2KOK 2 gs L = true) ∧ (∃ gs L, l2KOK 3 gs L = true) :=
  ⟨⟨kGs2, kL2, kOK2⟩, ⟨kGs3, kL3, kOK3⟩⟩

end Certificates

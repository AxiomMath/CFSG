module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
import Certificates.Kernel.OmegaEight.SB3884K2

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3884 CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3895 : (∃ gs L, l2KOK 4 gs L = true) ∧ (∃ gs L, l2KOK 5 gs L = true) :=
  ⟨⟨kGs4, kL4, kOK4⟩, ⟨kGs5, kL5, kOK5⟩⟩

end Certificates

module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
import Certificates.Kernel.OmegaEight.SB3884K3

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3884 CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3896 : (∃ gs L, l2KOK 6 gs L = true) ∧ (∃ gs L, l2KOK 7 gs L = true) :=
  ⟨⟨kGs6, kL6, kOK6⟩, ⟨kGs7, kL7, kOK7⟩⟩

end Certificates

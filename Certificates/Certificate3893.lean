module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
import Certificates.Kernel.OmegaEight.SB3884K0

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3884 CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3893 : (∃ gs L, l2KOK 0 gs L = true) ∧ (∃ gs L, l2KOK 1 gs L = true) :=
  ⟨⟨kGs0, kL0, kOK0⟩, ⟨kGs1, kL1, kOK1⟩⟩

end Certificates

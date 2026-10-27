module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data
import Certificates.Kernel.OmegaEight.SB3884T0
import Certificates.Kernel.OmegaEight.SB3884T1

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelO8.SB3884 CertificateChecks.KernelO8.SB3873 in
open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3884 : (∃ gs L, l2THOK 0 gs L = true) ∧ (∃ gs L, l2THOK 1 gs L = true) :=
  ⟨⟨thGs0, thPs0, th0⟩, ⟨thGs1, thPs1, th1⟩⟩

end Certificates

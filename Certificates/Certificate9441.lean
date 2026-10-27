module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
import Certificates.Kernel.Sp62W.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Sp62Local in
theorem certificate9441 : chkWD = true ∧ chkWL = true ∧ chkV = true :=
  ⟨KernelSp62W.chkWD_ok, KernelSp62W.chkWL_ok, KernelSp62W.chkV_ok⟩

end Certificates

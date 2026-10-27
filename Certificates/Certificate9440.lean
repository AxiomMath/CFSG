module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
import Certificates.Kernel.Sp62L.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Sp62Local in
theorem certificate9440 : chkT = true ∧ chkB = true ∧ chkE = true ∧ chkD = true :=
  ⟨KernelSp62L.chkT_ok, KernelSp62L.chkB_ok, KernelSp62L.chkE_ok, KernelSp62L.chkD_ok⟩

end Certificates

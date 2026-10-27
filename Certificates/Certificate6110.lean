
module

public import CFSG.Sporadic.Recognition.LyonsModelCP3Fact
import Certificates.Certificate6114
import Certificates.Kernel.LyModel.Cp3Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.LyonsSims.Ly0 in
theorem certificate6110 : (tabCheck = true) ∧ (coverCheck = true) ∧ (structCheck = true) ∧ (cp1Check = true) ∧
    (invCheck = true) ∧ (markCheck = true) ∧ Cp3Fact :=
  ⟨KernelLyModel.tabCheck_true, KernelLyModel.coverCheck_true certificate6114,
    KernelLyModel.structCheck_true certificate6114,
    KernelLyModel.cp1Check_true certificate6114,
    KernelLyModel.invCheck_true certificate6114,
    KernelLyModel.markCheck_true certificate6114,
    KernelLyModel.cp3Fact_true certificate6114⟩

end Certificates

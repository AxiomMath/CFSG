module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cCertInputs

public section

open CFSG.ComponentClassification.HSFLit.KD8c

namespace CertificateChecks.Batch22800

open CFSG.ComponentClassification.HSFLit.KD8c

private theorem chk10_0 : chk10 = true := by decide +kernel

private theorem chk11_1 : chk11 = true := by decide +kernel

private theorem chk20_2 : chk20 = true := by decide +kernel

private theorem chk21_3 : chk21 = true := by decide +kernel

private theorem chk70_4 : chk70 = true := by decide +kernel

private theorem chk71_5 : chk71 = true := by decide +kernel

private theorem chk50_6 : chk50 = true := by decide +kernel

private theorem chk51_7 : chk51 = true := by decide +kernel

private theorem chk61_8 : chk61 = true := by decide +kernel

end CertificateChecks.Batch22800

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HSFLit.KD8c in
theorem certificate22800 : chk10 = true ∧ chk11 = true ∧ chk20 = true ∧ chk21 = true ∧ chk70 = true ∧
    chk71 = true ∧ chk50 = true ∧ chk51 = true ∧ chk61 = true := by
  exact ⟨CertificateChecks.Batch22800.chk10_0, CertificateChecks.Batch22800.chk11_1, CertificateChecks.Batch22800.chk20_2, CertificateChecks.Batch22800.chk21_3,
    CertificateChecks.Batch22800.chk70_4, CertificateChecks.Batch22800.chk71_5, CertificateChecks.Batch22800.chk50_6, CertificateChecks.Batch22800.chk51_7,
    CertificateChecks.Batch22800.chk61_8⟩

end Certificates

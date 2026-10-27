module

public import Certificates.Data.SmithB45HM22HNor

public section

open CFSG.Quasithin.HM22

namespace CertificateChecks.Batch260417

open CFSG.Quasithin.HM22

private theorem hnor3a : hnorCheck3a = true := by
  decide +kernel

private theorem hnor3b : hnorCheck3b = true := by
  decide +kernel

private theorem hnor9 : hnorCheck9 = true := by
  decide +kernel

private theorem hnor24a : hnorCheck24a = true := by
  decide +kernel

private theorem hnor24b : hnorCheck24b = true := by
  decide +kernel

private theorem htrace : hTraceCheck = true := by
  decide +kernel

end CertificateChecks.Batch260417

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.HM22 in
theorem certificate260417 : hnorCheck3a = true ∧ hnorCheck3b = true ∧ hnorCheck9 = true ∧ hnorCheck24a = true ∧
    hnorCheck24b = true ∧ hTraceCheck = true :=
  ⟨CertificateChecks.Batch260417.hnor3a, CertificateChecks.Batch260417.hnor3b, CertificateChecks.Batch260417.hnor9, CertificateChecks.Batch260417.hnor24a,
    CertificateChecks.Batch260417.hnor24b, CertificateChecks.Batch260417.htrace⟩

end Certificates

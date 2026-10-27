module

public import CFSG.GH74.Filter.Lie.EvenSeriesInputs

public section

open CFSG.GH74.Filter.Lie

namespace CertificateChecks.Batch3953

open CFSG.GH74.Filter.Lie

private theorem witnessF4five_check_0 : witnessF4five.check = true := by
  decide +kernel

private theorem witnessE6five_check_1 : witnessE6five.check = true := by
  decide +kernel

private theorem witnessE7five_check_2 : witnessE7five.check = true := by
  decide +kernel

private theorem witnessE8five_check_3 : witnessE8five.check = true := by
  decide +kernel

end CertificateChecks.Batch3953

namespace Certificates

open CertificateChecks

open CFSG.GH74.Filter.Lie in
theorem certificate3953 : witnessF4five.check = true ∧ witnessE6five.check = true
    ∧ witnessE7five.check = true ∧ witnessE8five.check = true := by
  exact ⟨CertificateChecks.Batch3953.witnessF4five_check_0, CertificateChecks.Batch3953.witnessE6five_check_1,
    CertificateChecks.Batch3953.witnessE7five_check_2, CertificateChecks.Batch3953.witnessE8five_check_3⟩

end Certificates

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFCCheck
import CFSG.Certificates.Kernel.EvenSporDS81.FCSound
import Certificates.Kernel.EvenSporDS81.FCChecks

public section

namespace CertificateChecks.Batch25231

open CFSG.EvenSporadicStandard.TwoFi22.DS81 CertificateChecks.KernelEvenSporDS81 in
theorem fc_certificate_0 : fcCertificate = true :=
  CFSG.KC.EvenSporDS81.fcCheck_of_twin fc_cols fc_rest fc_tab fc_dist fc_fix

end CertificateChecks.Batch25231

namespace Certificates

open CertificateChecks

theorem certificate25231 : CFSG.EvenSporadicStandard.TwoFi22.DS81.fcCertificate = true := CertificateChecks.Batch25231.fc_certificate_0

end Certificates

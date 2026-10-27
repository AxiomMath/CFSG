module

public import Certificates.Data.E7Sec8Sylow
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivationE7Frames

public section

open CFSG.ComponentClassification.RankTwoExceptional.E7Sec8 CFSG.SeitzReduction

namespace CertificateChecks.Batch15093

open CFSG.ComponentClassification.RankTwoExceptional.E7Sec8 CFSG.SeitzReduction

private theorem check_y : e7SylowCheck oddDerivE7YFrame e7SylowCertY = true := by
  decide +kernel

private theorem check_z : e7SylowCheck oddDerivE7ZFrame e7SylowCertZ = true := by
  decide +kernel

private theorem check_u : e7SylowCheck oddDerivE7UFrame e7SylowCertU = true := by
  decide +kernel

private theorem check_v : e7SylowCheck oddDerivE7VFrame e7SylowCertV = true := by
  decide +kernel

end CertificateChecks.Batch15093

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.RankTwoExceptional.E7Sec8 CFSG.SeitzReduction in
theorem certificate15093 : e7SylowCheck oddDerivE7YFrame e7SylowCertY = true ∧
    e7SylowCheck oddDerivE7ZFrame e7SylowCertZ = true ∧
    e7SylowCheck oddDerivE7UFrame e7SylowCertU = true ∧
    e7SylowCheck oddDerivE7VFrame e7SylowCertV = true :=
  ⟨CertificateChecks.Batch15093.check_y, CertificateChecks.Batch15093.check_z, CertificateChecks.Batch15093.check_u, CertificateChecks.Batch15093.check_v⟩

end Certificates

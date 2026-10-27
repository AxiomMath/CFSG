module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsCocycleInputs

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.Blueprint CFSG.ComponentClassification.CentralCover

namespace CertificateChecks.Batch11000

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.Blueprint CFSG.ComponentClassification.CentralCover

private theorem cocycleCheck_eq_0 : cocycleCheck = true := by
  decide +kernel

private theorem diagCheck_eq_1 : diagCheck = true := by
  decide +kernel

private theorem autCheck_eq_2 : autCheck = true := by
  decide +kernel

end CertificateChecks.Batch11000

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.Blueprint CFSG.ComponentClassification.CentralCover in
theorem certificate11000 : (
cocycleCheck = true
)
    ∧ (
diagCheck = true
)
    ∧ (
autCheck = true
) := by
  exact ⟨CertificateChecks.Batch11000.cocycleCheck_eq_0, CertificateChecks.Batch11000.diagCheck_eq_1, CertificateChecks.Batch11000.autCheck_eq_2⟩

end Certificates

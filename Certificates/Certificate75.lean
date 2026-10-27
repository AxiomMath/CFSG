module

public import CFSG.LieType.Chevalley.RootOps.Instance
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch75

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem g2_tabCheck : tabCheck .G2 = true := by decide +kernel

private theorem g2_allValid : allValid .G2 = true := by decide +kernel

end CertificateChecks.Batch75

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate75 : (tabCheck .G2 = true)
    ∧ (allValid .G2 = true) := by
  exact ⟨CertificateChecks.Batch75.g2_tabCheck, CertificateChecks.Batch75.g2_allValid⟩

end Certificates

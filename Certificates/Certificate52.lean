module

public import CFSG.LieType.Chevalley.RootOps.Instance
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch52

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e6_tabCheck : tabCheck .E6 = true := by decide +kernel

private theorem e6_allValid : allValid .E6 = true := by decide +kernel

end CertificateChecks.Batch52

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate52 : (tabCheck .E6 = true)
    ∧ (allValid .E6 = true) := by
  exact ⟨CertificateChecks.Batch52.e6_tabCheck, CertificateChecks.Batch52.e6_allValid⟩

end Certificates

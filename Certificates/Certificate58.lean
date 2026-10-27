module

public import CFSG.LieType.Chevalley.RootOps.Instance
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch58

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e7_tabCheck : tabCheck .E7 = true := by decide +kernel

private theorem e7_allValid : allValid .E7 = true := by decide +kernel

end CertificateChecks.Batch58

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate58 : (tabCheck .E7 = true)
    ∧ (allValid .E7 = true) := by
  exact ⟨CertificateChecks.Batch58.e7_tabCheck, CertificateChecks.Batch58.e7_allValid⟩

end Certificates

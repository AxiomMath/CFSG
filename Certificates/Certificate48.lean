module

public import CFSG.LieType.Chevalley.RootOps.Instance
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch48

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem d4_tabCheck : tabCheck .D4 = true := by decide +kernel

private theorem d4_allValid : allValid .D4 = true := by decide +kernel

end CertificateChecks.Batch48

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate48 : (tabCheck .D4 = true)
    ∧ (allValid .D4 = true) := by
  exact ⟨CertificateChecks.Batch48.d4_tabCheck, CertificateChecks.Batch48.d4_allValid⟩

end Certificates

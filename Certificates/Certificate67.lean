module

public import CFSG.LieType.Chevalley.RootOps.Instance
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch67

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e8_tabCheck : tabCheck .E8 = true := by decide +kernel

private theorem e8_allValid : allValid .E8 = true := by decide +kernel

end CertificateChecks.Batch67

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate67 : (tabCheck .E8 = true)
    ∧ (allValid .E8 = true) := by
  exact ⟨CertificateChecks.Batch67.e8_tabCheck, CertificateChecks.Batch67.e8_allValid⟩

end Certificates

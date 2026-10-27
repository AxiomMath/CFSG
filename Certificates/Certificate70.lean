module

public import CFSG.LieType.Chevalley.RootOps.CertTools
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch70

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem f4_simpleRow_0 : simpleRow .F4 ⟨0, by decide⟩ = true := by decide +kernel

private theorem f4_simpleRow_1 : simpleRow .F4 ⟨1, by decide⟩ = true := by decide +kernel

private theorem f4_simpleRow_2 : simpleRow .F4 ⟨2, by decide⟩ = true := by decide +kernel

private theorem f4_simpleRow_3 : simpleRow .F4 ⟨3, by decide⟩ = true := by decide +kernel

end CertificateChecks.Batch70

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate70 : (simpleRow .F4 ⟨0, by decide⟩ = true)
    ∧ (simpleRow .F4 ⟨1, by decide⟩ = true)
    ∧ (simpleRow .F4 ⟨2, by decide⟩ = true)
    ∧ (simpleRow .F4 ⟨3, by decide⟩ = true) := by
  exact ⟨CertificateChecks.Batch70.f4_simpleRow_0, CertificateChecks.Batch70.f4_simpleRow_1, CertificateChecks.Batch70.f4_simpleRow_2, CertificateChecks.Batch70.f4_simpleRow_3⟩

end Certificates

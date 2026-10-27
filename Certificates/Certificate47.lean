module

public import CFSG.LieType.Chevalley.RootOps.CertTools
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch47

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem d4_simpleRow_0 : simpleRow .D4 ⟨0, by decide⟩ = true := by decide +kernel

private theorem d4_simpleRow_1 : simpleRow .D4 ⟨1, by decide⟩ = true := by decide +kernel

private theorem d4_simpleRow_2 : simpleRow .D4 ⟨2, by decide⟩ = true := by decide +kernel

private theorem d4_simpleRow_3 : simpleRow .D4 ⟨3, by decide⟩ = true := by decide +kernel

end CertificateChecks.Batch47

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate47 : (simpleRow .D4 ⟨0, by decide⟩ = true)
    ∧ (simpleRow .D4 ⟨1, by decide⟩ = true)
    ∧ (simpleRow .D4 ⟨2, by decide⟩ = true)
    ∧ (simpleRow .D4 ⟨3, by decide⟩ = true) := by
  exact ⟨CertificateChecks.Batch47.d4_simpleRow_0, CertificateChecks.Batch47.d4_simpleRow_1, CertificateChecks.Batch47.d4_simpleRow_2, CertificateChecks.Batch47.d4_simpleRow_3⟩

end Certificates

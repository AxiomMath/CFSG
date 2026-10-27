module

public import CFSG.LieType.Chevalley.RootOps.CertTools
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch51

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e6_simpleRow_0 : simpleRow .E6 ⟨0, by decide⟩ = true := by decide +kernel

private theorem e6_simpleRow_1 : simpleRow .E6 ⟨1, by decide⟩ = true := by decide +kernel

private theorem e6_simpleRow_2 : simpleRow .E6 ⟨2, by decide⟩ = true := by decide +kernel

private theorem e6_simpleRow_3 : simpleRow .E6 ⟨3, by decide⟩ = true := by decide +kernel

private theorem e6_simpleRow_4 : simpleRow .E6 ⟨4, by decide⟩ = true := by decide +kernel

private theorem e6_simpleRow_5 : simpleRow .E6 ⟨5, by decide⟩ = true := by decide +kernel

end CertificateChecks.Batch51

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate51 : (simpleRow .E6 ⟨0, by decide⟩ = true)
    ∧ (simpleRow .E6 ⟨1, by decide⟩ = true)
    ∧ (simpleRow .E6 ⟨2, by decide⟩ = true)
    ∧ (simpleRow .E6 ⟨3, by decide⟩ = true)
    ∧ (simpleRow .E6 ⟨4, by decide⟩ = true)
    ∧ (simpleRow .E6 ⟨5, by decide⟩ = true) := by
  exact ⟨CertificateChecks.Batch51.e6_simpleRow_0, CertificateChecks.Batch51.e6_simpleRow_1, CertificateChecks.Batch51.e6_simpleRow_2, CertificateChecks.Batch51.e6_simpleRow_3, CertificateChecks.Batch51.e6_simpleRow_4, CertificateChecks.Batch51.e6_simpleRow_5⟩

end Certificates

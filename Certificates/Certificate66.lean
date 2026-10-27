module

public import CFSG.LieType.Chevalley.RootOps.CertTools
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch66

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e8_simpleRow_0 : simpleRow .E8 ⟨0, by decide⟩ = true := by decide +kernel

private theorem e8_simpleRow_1 : simpleRow .E8 ⟨1, by decide⟩ = true := by decide +kernel

private theorem e8_simpleRow_2 : simpleRow .E8 ⟨2, by decide⟩ = true := by decide +kernel

private theorem e8_simpleRow_3 : simpleRow .E8 ⟨3, by decide⟩ = true := by decide +kernel

private theorem e8_simpleRow_4 : simpleRow .E8 ⟨4, by decide⟩ = true := by decide +kernel

private theorem e8_simpleRow_5 : simpleRow .E8 ⟨5, by decide⟩ = true := by decide +kernel

private theorem e8_simpleRow_6 : simpleRow .E8 ⟨6, by decide⟩ = true := by decide +kernel

private theorem e8_simpleRow_7 : simpleRow .E8 ⟨7, by decide⟩ = true := by decide +kernel

end CertificateChecks.Batch66

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate66 : (simpleRow .E8 ⟨0, by decide⟩ = true)
    ∧ (simpleRow .E8 ⟨1, by decide⟩ = true)
    ∧ (simpleRow .E8 ⟨2, by decide⟩ = true)
    ∧ (simpleRow .E8 ⟨3, by decide⟩ = true)
    ∧ (simpleRow .E8 ⟨4, by decide⟩ = true)
    ∧ (simpleRow .E8 ⟨5, by decide⟩ = true)
    ∧ (simpleRow .E8 ⟨6, by decide⟩ = true)
    ∧ (simpleRow .E8 ⟨7, by decide⟩ = true) := by
  exact ⟨CertificateChecks.Batch66.e8_simpleRow_0, CertificateChecks.Batch66.e8_simpleRow_1, CertificateChecks.Batch66.e8_simpleRow_2, CertificateChecks.Batch66.e8_simpleRow_3, CertificateChecks.Batch66.e8_simpleRow_4, CertificateChecks.Batch66.e8_simpleRow_5, CertificateChecks.Batch66.e8_simpleRow_6, CertificateChecks.Batch66.e8_simpleRow_7⟩

end Certificates

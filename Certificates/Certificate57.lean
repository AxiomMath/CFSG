module

public import CFSG.LieType.Chevalley.RootOps.CertTools
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch57

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e7_simpleRow_0 : simpleRow .E7 ⟨0, by decide⟩ = true := by decide +kernel

private theorem e7_simpleRow_1 : simpleRow .E7 ⟨1, by decide⟩ = true := by decide +kernel

private theorem e7_simpleRow_2 : simpleRow .E7 ⟨2, by decide⟩ = true := by decide +kernel

private theorem e7_simpleRow_3 : simpleRow .E7 ⟨3, by decide⟩ = true := by decide +kernel

private theorem e7_simpleRow_4 : simpleRow .E7 ⟨4, by decide⟩ = true := by decide +kernel

private theorem e7_simpleRow_5 : simpleRow .E7 ⟨5, by decide⟩ = true := by decide +kernel

private theorem e7_simpleRow_6 : simpleRow .E7 ⟨6, by decide⟩ = true := by decide +kernel

end CertificateChecks.Batch57

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate57 : (simpleRow .E7 ⟨0, by decide⟩ = true)
    ∧ (simpleRow .E7 ⟨1, by decide⟩ = true)
    ∧ (simpleRow .E7 ⟨2, by decide⟩ = true)
    ∧ (simpleRow .E7 ⟨3, by decide⟩ = true)
    ∧ (simpleRow .E7 ⟨4, by decide⟩ = true)
    ∧ (simpleRow .E7 ⟨5, by decide⟩ = true)
    ∧ (simpleRow .E7 ⟨6, by decide⟩ = true) := by
  exact ⟨CertificateChecks.Batch57.e7_simpleRow_0, CertificateChecks.Batch57.e7_simpleRow_1, CertificateChecks.Batch57.e7_simpleRow_2, CertificateChecks.Batch57.e7_simpleRow_3, CertificateChecks.Batch57.e7_simpleRow_4, CertificateChecks.Batch57.e7_simpleRow_5, CertificateChecks.Batch57.e7_simpleRow_6⟩

end Certificates

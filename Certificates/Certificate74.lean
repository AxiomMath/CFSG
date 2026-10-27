module

public import CFSG.LieType.Chevalley.RootOps.CertTools
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch74

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem g2_simpleRow_0 : simpleRow .G2 ⟨0, by decide⟩ = true := by decide +kernel

private theorem g2_simpleRow_1 : simpleRow .G2 ⟨1, by decide⟩ = true := by decide +kernel

end CertificateChecks.Batch74

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate74 : (simpleRow .G2 ⟨0, by decide⟩ = true)
    ∧ (simpleRow .G2 ⟨1, by decide⟩ = true) := by
  exact ⟨CertificateChecks.Batch74.g2_simpleRow_0, CertificateChecks.Batch74.g2_simpleRow_1⟩

end Certificates

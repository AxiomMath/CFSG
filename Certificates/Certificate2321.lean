
module

public import Certificates.Certificate2321Base
import all Certificates.Certificate2321Base

public import CFSG.Sporadic.ThSchreier.RigidityInputs
public meta import CFSG.Sporadic.ThSchreier.Enc8
import CFSG.Sporadic.Th.Max3.QuotientBase
import CFSG.Sporadic.ThSchreier.Enc8
meta import CFSG.Sporadic.ThSchreier.RigidityInputs

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

namespace CertificateChecks.Batch2321

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

end CertificateChecks.Batch2321

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 in
theorem certificate2321 : (mul8 (colMat8 B1enc B2enc 1) basisPInvEnc = id8)
    ∧ (∀ u < 256,
      mul8 (candEnc B1enc B2enc u) B1enc = mul8 B1enc (candEnc B1enc B2enc u) →
      mul8 (candEnc B1enc B2enc u) B2enc = mul8 B2enc (candEnc B1enc B2enc u) →
      candEnc B1enc B2enc u = zero8 ∨ candEnc B1enc B2enc u = id8
    )
    ∧ (∀ u < 256,
      mul8 (candEnc D1enc D2enc u) B1enc = mul8 D1enc (candEnc D1enc D2enc u) →
      mul8 (candEnc D1enc D2enc u) B2enc = mul8 D2enc (candEnc D1enc D2enc u) →
      candEnc D1enc D2enc u = zero8
    )
    ∧ (∀ v : Fin 8 → ZMod 2, vec8 (enc8 v) = v ∧ enc8 v < 256)
    ∧ (∀ x ∈ D1enc, x < 256)
    ∧ (∀ x ∈ D2enc, x < 256) := by
  exact ⟨CertificateChecks.Batch2321.enc_basisP_0, CertificateChecks.Batch2321.enc_commutant_1, CertificateChecks.Batch2321.enc_intertwiner_2, CertificateChecks.Batch2321.enc8_facts_3, CertificateChecks.Batch2321.intertwiner_D_hD1_4, CertificateChecks.Batch2321.intertwiner_D_hD2_5⟩

end Certificates

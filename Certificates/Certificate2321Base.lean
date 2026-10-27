
module

public import CFSG.Sporadic.ThSchreier.RigidityInputs
public meta import CFSG.Sporadic.ThSchreier.Enc8
import CFSG.Sporadic.Th.Max3.QuotientBase
import CFSG.Sporadic.ThSchreier.Enc8
meta import CFSG.Sporadic.ThSchreier.RigidityInputs

@[expose] public section

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

namespace CertificateChecks.Batch2321

private theorem enc_basisP_0 : mul8 (colMat8 B1enc B2enc 1) basisPInvEnc = id8 := by
  decide +kernel

private theorem enc_commutant_1 : ∀ u < 256,
    mul8 (candEnc B1enc B2enc u) B1enc = mul8 B1enc (candEnc B1enc B2enc u) →
    mul8 (candEnc B1enc B2enc u) B2enc = mul8 B2enc (candEnc B1enc B2enc u) →
    candEnc B1enc B2enc u = zero8 ∨ candEnc B1enc B2enc u = id8 := by
  decide +kernel

private theorem enc_intertwiner_2 : ∀ u < 256,
    mul8 (candEnc D1enc D2enc u) B1enc = mul8 D1enc (candEnc D1enc D2enc u) →
    mul8 (candEnc D1enc D2enc u) B2enc = mul8 D2enc (candEnc D1enc D2enc u) →
    candEnc D1enc D2enc u = zero8 := by
  decide +kernel

private theorem enc8_facts_3 : ∀ v : Fin 8 → ZMod 2, vec8 (enc8 v) = v ∧ enc8 v < 256 := by
  decide +kernel

private theorem intertwiner_D_hD1_4 : ∀ x ∈ D1enc, x < 256 := by
  decide +kernel

private theorem intertwiner_D_hD2_5 : ∀ x ∈ D2enc, x < 256 := by
  decide +kernel

end CertificateChecks.Batch2321

namespace Certificates

end Certificates

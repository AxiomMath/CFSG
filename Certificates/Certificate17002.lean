module

public import CFSG.Quasithin.Background.JonesParshallG2Two
public import CFSG.Quasithin.Background.B5FinOutAlt
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Quasithin.Recognition.CertU33Perm
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import CFSG.Quasithin.Background.B5FinG2U33Inputs
import Certificates.Certificate17028
import Certificates.Certificate8952
import Certificates.Certificate8953

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.CosetTable CFSG.Open commutatorElement

namespace CertificateChecks.Batch17002

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.CosetTable CFSG.Open commutatorElement

private theorem cmat_u33ImgL_0 (i : Fin 5) : cmat (u33ImgL i) = u33Mats i := by
  rw [u33ImgL, cmat_wordEval _ _ cmat_ab]
  revert i
  decide +kernel

private theorem u33Mats_mul_inv_1 (i : Fin 5) : u33Mats i * u33MatsInv i = 1 ∧ u33MatsInv i * u33Mats i = 1 := by
  revert i
  decide +kernel

private theorem u33Mats_rels_2 : ∀ w ∈ u33PresRels,
    (w.map fun x : Fin 5 × Bool => cond x.2 (u33Mats x.1) (u33MatsInv x.1)).prod = 1 := by
  decide +kernel

end CertificateChecks.Batch17002

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.CosetTable CFSG.Open commutatorElement in
theorem certificate17002 : (
∀ (i : Fin 5), cmat (u33ImgL i) = u33Mats i
)
    ∧ (
∀ (i : Fin 5), u33Mats i * u33MatsInv i = 1 ∧ u33MatsInv i * u33Mats i = 1
)
    ∧ (
 ∀ w ∈ u33PresRels,
    (w.map fun x : Fin 5 × Bool => cond x.2 (u33Mats x.1) (u33MatsInv x.1)).prod = 1 
) := by
  exact ⟨@CertificateChecks.Batch17002.cmat_u33ImgL_0, @CertificateChecks.Batch17002.u33Mats_mul_inv_1, @CertificateChecks.Batch17002.u33Mats_rels_2⟩

end Certificates

module

public import CFSG.Quasithin.Recognition.M12AscL2Inputs
public import Certificates.Certificate8950

public section

open CFSG CFSG.Quasithin Subgroup Equiv

namespace CertificateChecks.Batch17036

open CFSG CFSG.Quasithin Subgroup Equiv

private theorem D6l_nodup_0 : D6l.Nodup := by
  decide +kernel

private theorem D6l_mul_1 : ∀ d ∈ D6l, ∀ d' ∈ D6l, d * d' ∈ D6l := by
  decide +kernel

private theorem D6l_inv_2 : ∀ d ∈ D6l, d⁻¹ ∈ D6l := by
  decide +kernel

end CertificateChecks.Batch17036

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin Subgroup Equiv in
theorem certificate17036 : (
 D6l.Nodup 
)
    ∧ (
 ∀ d ∈ D6l, ∀ d' ∈ D6l, d * d' ∈ D6l 
)
    ∧ (
 ∀ d ∈ D6l, d⁻¹ ∈ D6l 
) := by
  exact ⟨@CertificateChecks.Batch17036.D6l_nodup_0, @CertificateChecks.Batch17036.D6l_mul_1, @CertificateChecks.Batch17036.D6l_inv_2⟩

end Certificates

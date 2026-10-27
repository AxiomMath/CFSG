module

public import CFSG.Quasithin.EmptyFaithful.S152FinRank
public import CFSG.Quasithin.EmptyFaithful.S152FinBasic
public import Certificates.Certificate3172
public import Certificates.Kernel.J4Q.Mat

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.S152Fin

namespace CertificateChecks.Batch17020

open CFSG CFSG.Quasithin CFSG.Quasithin.S152Fin

private theorem Wr_cube_comm_0 :  ∀ x y : Wr, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x  := by
  decide +kernel

private theorem Wr_cube_conj_1 :  ∀ x : Wr, x ^ 3 = 1 → x ≠ 1 →
    ∃ g : Wr, g * x * g⁻¹ ≠ 1 ∧ g * x * g⁻¹ ≠ x ∧ g * x * g⁻¹ ≠ x ^ 2  := by
  decide +kernel

private theorem Wr_card_cube_2 :  Fintype.card {x : Wr // x ^ 3 = 1} = 9  := by
  decide +kernel

end CertificateChecks.Batch17020

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.S152Fin in
theorem certificate17020 : (
 ∀ x y : Wr, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x 
)
    ∧ (
 ∀ x : Wr, x ^ 3 = 1 → x ≠ 1 →
    ∃ g : Wr, g * x * g⁻¹ ≠ 1 ∧ g * x * g⁻¹ ≠ x ∧ g * x * g⁻¹ ≠ x ^ 2 
)
    ∧ (
 Fintype.card {x : Wr // x ^ 3 = 1} = 9 
) := by
  exact ⟨@CertificateChecks.Batch17020.Wr_cube_comm_0, @CertificateChecks.Batch17020.Wr_cube_conj_1, @CertificateChecks.Batch17020.Wr_card_cube_2⟩

end Certificates

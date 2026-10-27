module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

open CFSG CFSG.Fischer

namespace CertificateChecks.Batch7057

open CFSG CFSG.Fischer

set_option maxHeartbeats 0 in
private theorem gl2_cube_of_pow_nine_0 :
    ∀ A : Matrix (Fin 2) (Fin 2) F4, A ^ 9 = 1 → A ^ 3 = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem gl2_scalar_of_conj_cube_1 :
    ∀ A : Matrix (Fin 2) (Fin 2) F4, A ^ 3 = 1 →
      (∀ B : Matrix (Fin 2) (Fin 2) F4, B.det ≠ 0 →
        (A * (B * A * (B.det⁻¹ • B.adjugate))) ^ 3 = 1) →
      ∃ c : F4, A = Matrix.scalar (Fin 2) c := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem gl2_semilinear_involutions_2 :
    ∀ P Q : Matrix (Fin 2) (Fin 2) F4,
      P * P.map (· ^ 2) = 1 → Q * Q.map (· ^ 2) = 1 → (P * Q.map (· ^ 2)).det = 1 →
        (P * Q.map (· ^ 2)) ^ 2 = 1 ∨ (P * Q.map (· ^ 2)) ^ 3 = 1 := by
  decide +kernel

end CertificateChecks.Batch7057

namespace Certificates

open CertificateChecks

open CFSG CFSG.Fischer in
theorem certificate7057 :
    (∀ A : Matrix (Fin 2) (Fin 2) F4, A ^ 9 = 1 → A ^ 3 = 1)
    ∧ (∀ A : Matrix (Fin 2) (Fin 2) F4, A ^ 3 = 1 →
       (∀ B : Matrix (Fin 2) (Fin 2) F4, B.det ≠ 0 →
         (A * (B * A * (B.det⁻¹ • B.adjugate))) ^ 3 = 1) →
       ∃ c : F4, A = Matrix.scalar (Fin 2) c)
    ∧ (∀ P Q : Matrix (Fin 2) (Fin 2) F4,
       P * P.map (· ^ 2) = 1 → Q * Q.map (· ^ 2) = 1 → (P * Q.map (· ^ 2)).det = 1 →
         (P * Q.map (· ^ 2)) ^ 2 = 1 ∨ (P * Q.map (· ^ 2)) ^ 3 = 1) := by
  exact ⟨CertificateChecks.Batch7057.gl2_cube_of_pow_nine_0, CertificateChecks.Batch7057.gl2_scalar_of_conj_cube_1,
    CertificateChecks.Batch7057.gl2_semilinear_involutions_2⟩

end Certificates

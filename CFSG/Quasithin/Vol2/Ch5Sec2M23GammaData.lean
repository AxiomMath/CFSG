module

public import CFSG.Fischer.F4
public meta import CFSG.Fischer.F4
public import Certificates.Certificate7057
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Quasithin.H13

open CFSG.Fischer

theorem gl2_cube_of_pow_nine :
    ∀ A : Matrix (Fin 2) (Fin 2) F4, A ^ 9 = 1 → A ^ 3 = 1 :=
  Certificates.certificate7057.1

theorem gl2_scalar_of_conj_cube :
    ∀ A : Matrix (Fin 2) (Fin 2) F4, A ^ 3 = 1 →
    (∀ B : Matrix (Fin 2) (Fin 2) F4, B.det ≠ 0 →
      (A * (B * A * (B.det⁻¹ • B.adjugate))) ^ 3 = 1) →
    ∃ c : F4, A = Matrix.scalar (Fin 2) c :=
  Certificates.certificate7057.2.1

theorem gl2_semilinear_involutions :
    ∀ P Q : Matrix (Fin 2) (Fin 2) F4,
    P * P.map (· ^ 2) = 1 → Q * Q.map (· ^ 2) = 1 → (P * Q.map (· ^ 2)).det = 1 →
      (P * Q.map (· ^ 2)) ^ 2 = 1 ∨ (P * Q.map (· ^ 2)) ^ 3 = 1 :=
  Certificates.certificate7057.2.2

end CFSG.Quasithin.H13

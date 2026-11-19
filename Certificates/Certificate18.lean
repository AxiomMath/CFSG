module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate18 : ∀ (x : Fin 23) (i : Fin 5) (_hx0 : x ≠ 0) (_hx1 : x ≠ 1),
      (t2 (S2 i • x))⁻¹ * S2 i * t2 x =
        ((evalGroupWord S3 (E2 x i) : H3) : H2) := by
  intro x i _hx0 _hx1
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro z
  fin_cases x <;> simp_all <;> fin_cases i <;> fin_cases z <;> decide

end Certificates

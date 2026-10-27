module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate20 : ∀ (x : Fin 23) (i : Fin 2) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2),
      (t3 (S3 i • x))⁻¹ * S3 i * t3 x =
        ((evalGroupWord S4 (E3 x i) : H4) : H3) := by
  intro x i hx0 hx1 hx2
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro z
  fin_cases x <;> simp_all <;> fin_cases i <;> fin_cases z <;> decide

end Certificates

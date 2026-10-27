module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate16 : ∀ (x : Fin 23) (i : Fin 4) (hx : x ≠ 0),
      (t1 (S1 i • x))⁻¹ * S1 i * t1 x =
        ((evalGroupWord S2 (E1 x i) : H2) : H1) := by
  intro x i hx
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro z
  fin_cases x <;> simp_all <;> fin_cases i <;> fin_cases z <;> decide

end Certificates

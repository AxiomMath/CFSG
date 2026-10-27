module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate23 : ∀ (x : Fin 23) (i : Fin 3) (hx : Q x),
      (t4 (S4 i • x))⁻¹ * S4 i * t4 x =
        ((evalGroupWord S5 (E4 x i) : H5) : H4) := by
  intro x i hx
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro z
  rcases hx with rfl | rfl | rfl <;> fin_cases i <;> fin_cases z <;> decide

end Certificates

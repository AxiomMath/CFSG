module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate28 : ∀ (i : Fin 4),
      (t5 (S5 i • (7 : Fin 23)))⁻¹ * S5 i * t5 7 = 1 := by
  intro i
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro z
  fin_cases i <;> fin_cases z <;> decide

end Certificates

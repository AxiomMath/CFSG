module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate14 : ∀ (x : Fin 23) (i : Fin 2),
      (t0 (S0 i • x))⁻¹ * S0 i * t0 x =
        ((evalGroupWord S1 (E0 x i) : H1) : H0) := by
  intro x i
  apply Subtype.ext
  apply Equiv.ext
  intro z
  fin_cases x <;> fin_cases i <;> fin_cases z <;> decide

end Certificates

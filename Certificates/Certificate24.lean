module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate24 : ∀ (i : Fin 4) (x : Fin 23), R x ↔ R (S5 i • x) := by
  intro i x
  fin_cases i <;> fin_cases x <;> simp [R] <;> decide

end Certificates

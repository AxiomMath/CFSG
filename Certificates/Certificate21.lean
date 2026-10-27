module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate21 : ∀ (i : Fin 3) (x : Fin 23), Q x ↔ Q (S4 i • x) := by
  intro i x
  fin_cases i <;> fin_cases x <;> simp [Q] <;> decide

end Certificates

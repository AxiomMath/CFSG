module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate15 : ∀ (x : Fin 23) (hx : x ≠ 0), t1 x • (1 : Fin 23) = x := by
  intro x hx
  fin_cases x <;> simp_all <;> decide

end Certificates

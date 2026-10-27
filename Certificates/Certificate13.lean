module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate13 : ∀ (x : Fin 23), t0 x • (0 : Fin 23) = x := by
  intro x
  fin_cases x <;> decide

end Certificates

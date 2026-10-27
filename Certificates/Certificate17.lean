module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate17 : ∀ (x : Fin 23) (hx0 : x ≠ 0) (hx1 : x ≠ 1),
      t2 x • (2 : Fin 23) = x := by
  intro x hx0 hx1
  fin_cases x <;> simp_all <;> decide

end Certificates

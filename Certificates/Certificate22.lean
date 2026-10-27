module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate22 : ∀ (x : Fin 23) (hx : Q x), t4 x • (4 : Fin 23) = x := by
  intro x hx
  rcases hx with rfl | rfl | rfl <;> decide

end Certificates

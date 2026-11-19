module

public import Certificates.Data.M23Transversals

public section

open CFSG.M23 CFSG.M23.M23Group
open scoped Pointwise

namespace Certificates

open CFSG.M23 CFSG.M23.M23Group in
open scoped Pointwise in
theorem certificate22 : ∀ (x : Fin 23) (_hx : Q x), t4 x • (4 : Fin 23) = x := by
  intro x _hx
  rcases _hx with rfl | rfl | rfl <;> decide

end Certificates

module

public import CFSG.Quasithin.Background.HSporLatM23Sg
import Certificates.Kernel.M23Dc.Facts
import Certificates.Kernel.M23Dc.NoFifteen

public section

namespace Certificates

open CFSG.KD.M23Dc

open CFSG.Quasithin.H.MathieuLat in
theorem certificate1089001 : ∀ j, j = 2 ∨ j = 5 → ∀ z ∈ m23Member j, orderOf z ≠ 15 :=
  fun j hj z hz => m23K_noFifteen hj z (by rw [m23K_Y_eq]; exact hz)

end Certificates

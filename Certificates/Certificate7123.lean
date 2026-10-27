module

public import CFSG.Quasithin.Background.E2TwoProofSporM23Inputs
public import CFSG.Quasithin.Background.HSporLatM23Sg
import Certificates.Kernel.M23Dc.Facts
import Certificates.Kernel.M23Dc.Sigma

public section

namespace Certificates

open CFSG.KD.M23Dc

open CFSG.Quasithin.H.MathieuLat in
theorem certificate7123 : ∀ j < 16, ∀ jj < 16, (m23Member j ≤ m23Member jj ↔ jj ∈ m23Incl[j]!) :=
  fun j hj jj hjj => by
    rw [← m23K_Y_eq, ← m23K_Y_eq]
    exact m23K_Y_le_iff hj hjj

end Certificates

module

public import Certificates.Data.M23T3
public import CFSG.Quasithin.Background.HSporLatM23Sg
import Certificates.Kernel.M23Dc.Facts
import Certificates.Kernel.M23Dc.T3

public section

namespace Certificates

open CFSG.KD.M23Dc

open CFSG.Quasithin.H.MathieuLat in
theorem certificate7160 :
    (∀ j ∈ [10, 11, 12, 13, 14], ¬ m23Member j ≤
      Subgroup.normalizer (m23SylTwo : Set ↥CFSG.Blueprint.NativeSporadic.M23)) ∧ M23T3.e9 :=
  ⟨fun j hj => by
    rw [← m23K_Y_eq, ← m23K_S_eq]
    exact m23K_notNormal hj, t3e9⟩

end Certificates

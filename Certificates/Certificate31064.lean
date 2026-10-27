module

public import CFSG.Sporadic.He.Setup
import Certificates.Kernel.He31064.Final

public section

namespace Certificates

theorem certificate31064 : ∃ R : Subgroup ↥CFSG.Sporadic.He.J,
    Nat.card R = 6174 ∧ ∀ Y : Subgroup ↥CFSG.Sporadic.He.J, R ≤ Y → Y = R ∨ Y = ⊤ :=
  CFSG.KD.He31064.maximal

end Certificates

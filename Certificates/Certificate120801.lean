module

public import CFSG.Sporadic.Co1.Asch54PairDefs
import Certificates.Kernel.Co1Sub.OrderT

public section

namespace Certificates

theorem certificate120801 : Nat.card CFSG.Sporadic.Co1Sub.T₀ = 2 ^ 21 := by
  have e : CFSG.Sporadic.Co1Sub.T₀ = CFSG.KD.Co1Sub.subG CFSG.KD.Co1Sub.tI := rfl
  rw [e]
  exact CFSG.KD.Co1Sub.card_subG_tI

end Certificates

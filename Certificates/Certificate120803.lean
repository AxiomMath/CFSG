module

public import CFSG.Sporadic.Co1.Asch54PairDefs
import Certificates.Kernel.Co1Sub.OrderAB

public section

namespace Certificates

theorem certificate120803 : Nat.card CFSG.Sporadic.Co1Sub.B₀ = 405 * 2 ^ 21 := by
  have e : CFSG.Sporadic.Co1Sub.B₀ = CFSG.KD.Co1Sub.subG CFSG.KD.Co1Sub.bI := rfl
  rw [e]
  exact CFSG.KD.Co1Sub.card_subG_bI

end Certificates

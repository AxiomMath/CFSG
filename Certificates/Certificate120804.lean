module

public import CFSG.Sporadic.Co1.Asch54PairDefs
import Certificates.Kernel.Co1Sub.OrderAB

public section

namespace Certificates

theorem certificate120804 : CFSG.Sporadic.Co1Sub.A₀ ⊔ CFSG.Sporadic.Co1Sub.B₀ = ⊤ := by
  have eA : CFSG.Sporadic.Co1Sub.A₀ = CFSG.KD.Co1Sub.subG CFSG.KD.Co1Sub.aI := rfl
  have eB : CFSG.Sporadic.Co1Sub.B₀ = CFSG.KD.Co1Sub.subG CFSG.KD.Co1Sub.bI := rfl
  rw [eA, eB]
  exact CFSG.KD.Co1Sub.sup_subG_aI_bI

end Certificates

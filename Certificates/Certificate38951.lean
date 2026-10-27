module

public import CFSG.GF2Type.Widths1112.Co2FormDefs
import Certificates.Kernel.Co2W11.OrbGlue

public section

open CFSG.GF2Type.Widths1112 CFSG.Sporadic.SmallF2

public section

namespace Certificates

open CertificateChecks

open CFSG.GF2Type.Widths1112 CFSG.Sporadic.SmallF2 in
theorem certificate38951 : (∀ v : Vec22, v ≠ 0 → q₀₂ v = 0 → v ∈ co2Orbit 0 ∨ v ∈ co2Orbit 1 ∨ v ∈ co2Orbit 2) ∧
    Submodule.span (ZMod 2) (co2Orbit 0) = ⊤ :=
  ⟨KernelCo2W11.orb_cover, KernelCo2W11.orb_span⟩

end Certificates

end

end

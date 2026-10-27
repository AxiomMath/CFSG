module

public import CFSG.LargeExtraspecial.SL4ModEmbed
public import Certificates.Data.SL4ModNoneData
import Certificates.Kernel.SL4ModNone.Facts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace Certificates

open CertificateChecks

open CFSG.LargeExtraspecial.SL4Mod in
theorem certificate705102 : ∀ d ∈ CFSG.LargeExtraspecial.SL4Mod.Native.noneDims,
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V],
      Module.finrank (ZMod 2) V = d → ∀ ρ : SL4 →* (V ≃ₗ[ZMod 2] V), ¬ IsIrredGen ρ :=
  fun _ hd _ _ _ _ hV ρ =>
    CFSG.LargeExtraspecial.SL4Mod.no_irred_of_noneCertData KernelSL4ModNone.noneCertData hd hV ρ

end Certificates

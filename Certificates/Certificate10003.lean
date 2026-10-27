module

public import CFSG.LargeExtraspecial.SL4ModEmbed
import Certificates.Kernel.SL4Mod.Facts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace Certificates

open CertificateChecks

theorem certificate10003 : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V],
    Module.finrank (ZMod 2) V = 8 → ∀ ρ : CFSG.LargeExtraspecial.SL4Mod.SL4 →* (V ≃ₗ[ZMod 2] V),
      ¬ CFSG.LargeExtraspecial.SL4Mod.IsIrredGen ρ :=
  fun _ _ _ _ hV ρ =>
    CFSG.LargeExtraspecial.SL4Mod.not_isIrredGen_of KernelSL4Mod.spinCertData hV ρ

end Certificates

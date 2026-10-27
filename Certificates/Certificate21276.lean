module

public import CFSG.LargeExtraspecial.S14SMKTransFp
import Certificates.Kernel.SmithEK.GlueCand

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithE CFSG.Fischer.Native CFSG.LargeExtraspecial.S14.SMK CFSG.LargeExtraspecial.SMod20 in
theorem certificate21276 : ∀ j < 5, ∀ a < 512,
    ∀ (A : V ≃ₗ[ZMod 2] V) (π : Equiv.Perm (Fin 693)), InvHyp A π →
      IsTab (candT tvTabs uaPts[0]! (liftTab tvTabs j) a) π → InvConcl A π :=
  fun _ hj _ ha _ _ h hc => KernelSmithEK.cand_concl hj ha h hc

end Certificates

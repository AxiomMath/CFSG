module

public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
public import CFSG.Blueprint.NativeSporadic
import CFSG.Sporadic.Recognition.HeMultiplierBounds
import Certificates.Kernel.HeMult.Bounds
import Certificates.Kernel.HeMult.Tab

public section

namespace Certificates

open CertificateChecks

theorem certificate6103 :
    Nat.card (CFSG.Open.griessHopfMultiplier CFSG.Blueprint.NativeSporadic.He) = 1 :=
  CFSG.Sporadic.Recognition.HeMultiplier.card_griessHopfMultiplier_He_of_bounds
    CFSG.KD.HeMult.heTab_ok KernelHeMult.card_presented KernelHeMult.card_cover

end Certificates

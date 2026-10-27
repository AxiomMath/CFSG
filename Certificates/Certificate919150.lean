module

public import Certificates.Data.Foote82OmegaSixAut
import Certificates.Kernel.Misc.OmegaSix.FinalF

public section

namespace Certificates

open CFSG.CGT.Foote82.OmegaSix in
theorem certificate919150 :
    (fiveCheck () = true)
    ∧ (CFSG.CGT.Foote82.OmegaSix.pairCheck () = true) :=
  ⟨CFSG.KD.OmegaSix.fiveCheck_ok, CFSG.KD.OmegaSix.pairCheck_ok⟩

end Certificates

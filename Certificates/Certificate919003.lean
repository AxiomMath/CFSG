module

public import Certificates.Data.Foote82OmegaSixNorm
import Certificates.Kernel.Misc.OmegaSix.TransFacts

public section

namespace Certificates

open CFSG.CGT.Foote82.OmegaSix in
theorem certificate919003 :
    (transCheck () = true)
    ∧ (countCheck () = true) :=
  ⟨CFSG.KD.OmegaSix.Trans.transCheck_ok, CFSG.KD.OmegaSix.Trans.countCheck_ok⟩

end Certificates

module

public import Certificates.Data.Foote82OmegaSixTI
import Certificates.Kernel.Misc.OmegaSix.TIFacts

public section

namespace Certificates

open CFSG.CGT.Foote82.OmegaSix in
theorem certificate919010 : tiCheck () = true := CFSG.KD.OmegaSix.tiCheck_ok

end Certificates

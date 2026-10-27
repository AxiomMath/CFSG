module

public import Certificates.Kernel.Misc.OmegaSix.FinalMx

public section

open CFSG.CGT.Foote82.OmegaSix

namespace Certificates

open CFSG.CGT.Foote82.OmegaSix in
theorem certificate919005 :
    (maxMatCheck () = true)
    ∧ (maxMemCheck () = true)
    ∧ (crEnumCheck () = true)
    ∧ (maxGen1Check () = true)
    ∧ (maxGen2Check () = true)
    ∧ (maxCosetCheck () = true)
    ∧ (maxReflCheck () = true) :=
  ⟨CFSG.KD.OmegaSix.maxMatCheck_ok, CFSG.KD.OmegaSix.maxMemCheck_ok,
    CFSG.KD.OmegaSix.crEnumCheck_ok, CFSG.KD.OmegaSix.maxGen1Check_ok,
    CFSG.KD.OmegaSix.maxGen2Check_ok, CFSG.KD.OmegaSix.maxCosetCheck_ok,
    CFSG.KD.OmegaSix.maxReflCheck_ok⟩

end Certificates

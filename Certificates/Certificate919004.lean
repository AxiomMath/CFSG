module

public import Certificates.Kernel.Misc.OmegaSix.FinalA

public section

open CFSG.CGT.Foote82.OmegaSix

namespace Certificates

open CFSG.CGT.Foote82.OmegaSix in
theorem certificate919004 :
    (reflCheck () = true)
    ∧ (oEnumCheck () = true)
    ∧ (CFSG.CGT.Foote82.OmegaSix.repCheck () = true)
    ∧ (classCheck () = true)
    ∧ (centCheck () = true) :=
  ⟨CFSG.KD.OmegaSix.reflCheck_ok, CFSG.KD.OmegaSix.oEnumCheck_ok,
    CFSG.KD.OmegaSix.repCheck_ok, CFSG.KD.OmegaSix.classCheck_ok,
    CFSG.KD.OmegaSix.centCheck_ok⟩

end Certificates

end

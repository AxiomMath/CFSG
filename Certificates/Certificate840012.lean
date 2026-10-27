module

public import CFSG.CGT.Harada80.OmegaEightCheck
import Certificates.Kernel.Om8K.Glue

public section

namespace Certificates

open CFSG.CGT.Harada80.OmegaEight in
theorem certificate840012 : nsCheck = true ∧ genCheck = true ∧ relCheck = true ∧ wordCheck = true ∧ foxCheck = true :=
  ⟨CFSG.KC.Om8K.nsCheck_eq, CFSG.KC.Om8K.genCheck_eq, CFSG.KC.Om8K.relCheck_eq,
    CFSG.KC.Om8K.wordCheck_eq, CFSG.KC.Om8K.foxCheck_eq⟩

end Certificates

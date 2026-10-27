module

public import Certificates.Kernel.Misc.SylowG2.Final

public section

open CFSG.CGT.Foote82.CaseIIG2Aux

namespace Certificates

open CFSG.CGT.Foote82.CaseIIG2Aux in
theorem certificate919101 :
    (pEnumCheck () = true)
    ∧ (pAutCheck () = true)
    ∧ (qEnumCheck () = true)
    ∧ (qAutCheck () = true) :=
  ⟨CFSG.KD.SylowG2.pEnumCheck_ok, CFSG.KD.SylowG2.pAutCheck_ok, CFSG.KD.SylowG2.qEnumCheck_ok,
    CFSG.KD.SylowG2.qAutCheck_ok⟩

end Certificates

end

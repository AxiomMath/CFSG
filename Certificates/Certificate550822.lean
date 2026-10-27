module

public import Certificates.Data.Sp62RecCR1NA
import Certificates.Kernel.Misc.YamakiNA.Final

public section

namespace Certificates

open CFSG.KD.YamakiNA

open CFSG.ClassicalInvolution.Sp62Rec in
theorem certificate550822 :
    (centA0Check () = true)
    ∧ (normA0Check () = true)
    ∧ (wCheck () = true)
    ∧ (stabWCheck () = true)
    ∧ (centAlphaCheck () = true)
    ∧ (sylMeetCheck () = true)
    ∧ (orbCheck () = true)
    ∧ (e8Check () = true)
    ∧ (sevenCheck () = true)
    ∧ (rhoMatCheck () = true)
    ∧ (rhoKerCheck () = true)
    ∧ (alphaClassCheck () = true) :=
  ⟨centA0Check_holds, normA0Check_holds, wCheck_holds, stabWCheck_holds, centAlphaCheck_holds,
    sylMeetCheck_holds, orbCheck_holds, e8Check_holds, sevenCheck_holds, na550822rm,
    rhoKerCheck_holds, alphaClassCheck_holds⟩

end Certificates

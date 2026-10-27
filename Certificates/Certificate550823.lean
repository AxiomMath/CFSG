module

public import Certificates.Data.Sp62RecCR1CE
import Certificates.Kernel.Misc.YamakiCE.Final

public section

namespace Certificates

open CFSG.KD.YamakiCE

open CFSG.ClassicalInvolution.Sp62Rec in
theorem certificate550823 :
    (ceEnumCheck () = true)
    ∧ (v0Check () = true)
    ∧ (centE0Check () = true)
    ∧ (e64Check () = true)
    ∧ (a6Check () = true)
    ∧ (commCheck () = true) :=
  ⟨ceEnumCheck_holds, v0Check_holds, centE0Check_holds, e64Check_holds, a6Check_holds,
    commCheck_holds⟩

end Certificates

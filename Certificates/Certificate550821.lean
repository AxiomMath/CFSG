module

public import Certificates.Data.Sp62RecCR1
import Certificates.Kernel.Misc.YamakiA0.Final

public section

namespace Certificates

open CFSG.ClassicalInvolution.Sp62Rec in
theorem certificate550821 :
    (a0EnumCheck () = true)
    ∧ (a0AbelCheck () = true)
    ∧ (hhatAlphaCheck () = true)
    ∧ (fourCheck () = true) :=
  CFSG.KD.YamakiA0.cert550821_ok

end Certificates

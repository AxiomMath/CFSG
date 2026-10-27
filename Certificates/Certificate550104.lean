module

public import Certificates.Data.Z6NACount
import Certificates.Kernel.Misc.YamakiLbar.Final

public section

namespace Certificates

open CFSG.ClassicalInvolution.Sp62Rec in
theorem certificate550104 :
    (z6LbarCheck () = true)
    ∧ (z6OrbCheck () = true)
    ∧ (z6NormCheck () = true) :=
  CFSG.KD.YamakiLbar.cert550104_ok

end Certificates

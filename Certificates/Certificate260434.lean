module

public import CFSG.Certificates.Kernel.B45AmalSound
import Certificates.Kernel.C260434.Amal

public section

namespace Certificates

open CFSG.Quasithin.B45Mat.Ind in
theorem certificate260434 :
    amalOK = true :=
  CFSG.KC.B45Ind.amalOK_eq.trans CFSG.KD.C260434.amal

end Certificates

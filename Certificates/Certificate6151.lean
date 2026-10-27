
module

public import Certificates.Data.ONanB2A6
import CFSG.Certificates.Kernel.ONanA6Sound
import Certificates.Kernel.ONanA6.Codes
import Certificates.Kernel.ONanA6.Checks
import Certificates.Kernel.ONanA6.Mem

public section

namespace Certificates

open CFSG.OddStandard.ONanRec.A6C in
theorem certificate6151 : a6MirrorCheck = true :=
  CFSG.KC.ONanA6.s6151 CFSG.KD.ONanA6.hl CFSG.KD.ONanA6.hr CFSG.KD.ONanA6.hg
    ((CFSG.KC.LQT.S.memL_iff _ _).1 CFSG.KD.ONanA6.hu0) CFSG.KD.ONanA6.hk

end Certificates

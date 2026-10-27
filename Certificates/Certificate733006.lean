module

public import Certificates.Data.G24IdentWit
import CFSG.Certificates.Kernel.G24Wit.Sound
import Certificates.Kernel.G24Wit.Check
import Certificates.Kernel.Misc.G24Facts

public section

namespace Certificates

theorem certificate733006 : CFSG.Quasithin.St84.G24Wit.witCheck () = true :=
  CFSG.KC.G24Wit.witCheck_of_witK CFSG.KD.Misc.G24.bG CFSG.KD.Misc.G24.k44
    CFSG.KC.G24Wit.ch733006_wit

end Certificates

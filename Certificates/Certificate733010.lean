module

public import CFSG.Quasithin.Recognition.St84.G24ModelChevFacts
public import CFSG.Quasithin.Recognition.St84.G24RadFacts
import Certificates.Kernel.G24B.Rad

public section

namespace Certificates

theorem certificate733010 :     CFSG.Quasithin.F112R.St84.G24M.ChevFacts → CFSG.Quasithin.F112R.St84.G24M.RadFacts :=
  fun hC => CFSG.KD.G24B.radFacts hC

end Certificates

module

public import CFSG.Quasithin.Recognition.St84.G24BorelFacts
import Certificates.Kernel.G24B.Borel
public import CFSG.Quasithin.Recognition.St84.G24ModelChevFacts

public section

namespace Certificates

theorem certificate733008 :     CFSG.Quasithin.F112R.St84.G24M.ChevFacts → CFSG.Quasithin.F112R.St84.G24M.BorelFacts :=
  fun hC => CFSG.KD.G24B.borelFacts hC

end Certificates

module

public import CFSG.Quasithin.Recognition.St84.G24BorelFacts
import Certificates.Kernel.G24B.Normal
public import CFSG.Quasithin.Recognition.St84.G24ModelChevFacts

public section

namespace Certificates

theorem certificate733011 :     CFSG.Quasithin.F112R.St84.G24M.ChevFacts → CFSG.Quasithin.F112R.St84.G24M.NormalFacts :=
  fun hC => CFSG.KD.G24B.normalFacts hC

end Certificates

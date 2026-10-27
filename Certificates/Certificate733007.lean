module

public import CFSG.Quasithin.Recognition.St84.G24ModelChevFacts
public import CFSG.Quasithin.Recognition.St84.G24DecompFacts
import Certificates.Kernel.G24B.Decomp

public section

namespace Certificates

theorem certificate733007 :     CFSG.Quasithin.F112R.St84.G24M.ChevFacts → CFSG.Quasithin.F112R.St84.G24M.Facts →
      ∀ W : CFSG.Quasithin.F112R.St84.G24M.Witnesses, CFSG.Quasithin.F112R.St84.G24M.DecompFacts W :=
  fun hC hM W => CFSG.KD.G24B.decompFacts hC hM W

end Certificates

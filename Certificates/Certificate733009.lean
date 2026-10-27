module

public import CFSG.Quasithin.Recognition.St84.G24ModelChevFacts
public import CFSG.Quasithin.Recognition.St84.G24ModelFrameFacts
import Certificates.Kernel.G24B.Frames

public section

namespace Certificates

theorem certificate733009 :     CFSG.Quasithin.F112R.St84.G24M.ChevFacts → CFSG.Quasithin.F112R.St84.G24M.FrameFacts :=
  fun hC => CFSG.KD.G24B.frameFacts hC

end Certificates

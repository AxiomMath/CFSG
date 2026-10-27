module

public import Certificates.Data.Kernel.Co1K105.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Co1K105

open CFSG.KC.SLD2

theorem glob : globOK C D = true := by
  quickRfl

theorem frest : fRestOK C D = true := by
  quickRfl

theorem ridx : rootIdxOK C D = true := by
  quickRfl

theorem lens : (Nat.beq D.bo.length 0 && Nat.beq D.R1.length 8 && Nat.beq D.roots.length 1) =
    true := by
  quickRfl

end CFSG.KD.Co1K105

end

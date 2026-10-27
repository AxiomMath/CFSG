module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafSel
import Certificates.Kernel.ExcExt.InLSelAll
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712516 : InLLeafOrSelCases (excRaw 4) :=
  CFSG.ExcExtK.inLLeafOrSelCases_four

end Certificates

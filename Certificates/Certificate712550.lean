
module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameDefs
import Certificates.Kernel.ExcExt.InLNbrAll

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame in
theorem certificate712550 : ∀ m : Fin 6, NbrWeylData (excRaw m) :=
  CFSG.ExcExtK.nbrWeylData_all

end Certificates

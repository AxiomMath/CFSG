
module


public import Certificates.Certificate712525
public import Certificates.Data.CFSGNative.ExcCensus.Core

public section

namespace CFSG.StandardType.GGQ2Frame

namespace ExcRaw

variable {m : Fin 6} {T : Chk.Tabs}

theorem inLCommonCases_excRaw_four :
    InLCommonCases (excRaw 4) :=
  (inLCommonCases_iff_forall _).mpr Certificates.certificate712525

end ExcRaw

end CFSG.StandardType.GGQ2Frame

end


module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrExcBase

public import Certificates.Certificate712550
public import Certificates.Data.CFSGNative.ExcCensus.Nbr
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusLin
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameAut
import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawInternal

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

noncomputable section

variable {m : Fin 6} {T : Chk.Tabs} {w : Chk.LinW}

theorem nbrWeylData_excRaw (m : Fin 6) :
    NbrWeylData (excRaw m) :=
  Certificates.certificate712550 m

end

end CFSG.StandardType.GGQ2Frame.ExcRaw

end

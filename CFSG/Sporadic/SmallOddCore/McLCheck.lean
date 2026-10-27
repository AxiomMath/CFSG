module

public import CFSG.Sporadic.SmallOddCore.McLData
public import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public import CFSG.Sporadic.SmallOddCore.McLCheckInputs
public import Certificates.Certificate2284

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2.Native

theorem mcl_stabOK : mclStabOK = true :=
  Certificates.certificate2284.1

theorem mcl_centDataOK :
    centDataOK 275 898128000 120000 mclPGTbls mclPGInvTbls mclSift mclOuterTbl mclSylowGenTbls
      mclSylowOrder mclRows = true :=
  Certificates.certificate2284.2

end CFSG.Sporadic.SmallOddCore

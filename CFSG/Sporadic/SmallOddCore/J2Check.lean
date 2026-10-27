
module

public import CFSG.Sporadic.SmallOddCore.J2CheckBase

public import CFSG.Sporadic.SmallOddCore.J2Data
public import CFSG.Sporadic.Schreier.PairJ2Check
public meta import CFSG.Sporadic.SmallOddCore.J2Data
public meta import CFSG.Sporadic.Schreier.PairJ2Check
public import CFSG.Sporadic.SmallOddCore.J2CheckInputs
public import Certificates.Certificate2278

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native

theorem j2_stabOK : j2StabOK = true :=
  Certificates.certificate2278.1

theorem j2_centDataOK :
    centDataOK 315 604800 3000 j2PGTbls j2PGInvTbls j2Sift j2OuterTbl j2SylowGenTbls j2SylowOrder
      j2Rows = true :=
  Certificates.certificate2278.2

end CFSG.Sporadic.SmallOddCore

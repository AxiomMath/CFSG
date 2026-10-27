module

public import CFSG.Sporadic.SmallOddCore.CentData
public import CFSG.Sporadic.Schreier.Co3SylowCheck
public meta import CFSG.Sporadic.SmallOddCore.CentData
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck
public import CFSG.Sporadic.SmallOddCore.Co3FusionCheckInputs
public import Certificates.Certificate2271

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Schreier.Co3 CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem co3_fusionOK : co3FusionOK = true :=
  Certificates.certificate2271

end CFSG.Sporadic.SmallOddCore

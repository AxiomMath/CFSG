module

public import CFSG.Sporadic.SmallOddCore.J2Check
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public meta import CFSG.Sporadic.SmallOddCore.J2Check
public meta import CFSG.Sporadic.SmallOddCore.LocalCheck
public import CFSG.Sporadic.SmallOddCore.J2LocalCheckInputs
public import Certificates.Certificate2280

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem j2_DOK : j2DOK = true :=
  Certificates.certificate2280.1

theorem j2_QOK : j2QOK = true :=
  Certificates.certificate2280.2.1

theorem j2_D_noncomm :
    commTT 315 (wordTbl 315 j2C1Gens [3, 2]) (wordTbl 315 j2C1Gens [2, 4, 2, 4]) = false :=
  Certificates.certificate2280.2.2

end CFSG.Sporadic.SmallOddCore

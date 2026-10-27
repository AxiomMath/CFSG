module

public import CFSG.Sporadic.HNOddCore.SixData
public import CFSG.Sporadic.HNOddCore.SCheck
public import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNOddCore.SixData
public meta import CFSG.Sporadic.HNOddCore.SCheck
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public import CFSG.Sporadic.HNOddCore.SixCheckInputs
public import Certificates.Certificate2092

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

theorem six_cert : sixChecks = true :=
  Certificates.certificate2092

end CFSG.Sporadic.HNOddCore.Native

module

public import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
public import CFSG.Sporadic.FischerOddCore.Fi22CTICheckInputs
public import Certificates.Certificate2064

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

theorem cti_check : ctiChecks = true :=
  Certificates.certificate2064

end CFSG.Sporadic.FischerOddCore

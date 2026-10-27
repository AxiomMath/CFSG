
module

public import CFSG.Sporadic.HNOddCore.WCheckBase

public import CFSG.Sporadic.HNOddCore.PCheck
public meta import CFSG.Sporadic.HNOddCore.PCheck
public import CFSG.Sporadic.HNOddCore.WCheckInputs
public import Certificates.Certificate2093

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native

theorem wit_cert : witCoverChecks = true :=
  Certificates.certificate2093

end CFSG.Sporadic.HNOddCore.Native

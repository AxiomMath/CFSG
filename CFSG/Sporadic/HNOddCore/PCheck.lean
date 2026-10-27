
module

public import CFSG.Sporadic.HNOddCore.PCheckBase

public import CFSG.Sporadic.HNOddCore.QCheck
public import Std.Data.HashMap
public meta import CFSG.Sporadic.HNOddCore.QCheck
public meta import Std.Data.HashMap
public import CFSG.Sporadic.HNOddCore.PCheckInputs
public import Certificates.Certificate2088
public import CFSG.Sporadic.HNSchreier.SylowCheck

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native

theorem sylow_cert : sylowChecks = true :=
  Certificates.certificate2088

end CFSG.Sporadic.HNOddCore.Native


module

public import CFSG.Sporadic.HNOddCore.LCheckBase

public import CFSG.Sporadic.HNOddCore.XCheck
public import CFSG.Sporadic.HNOddCore.PCheck
public meta import CFSG.Sporadic.HNOddCore.XCheck
public meta import CFSG.Sporadic.HNOddCore.PCheck
public import CFSG.Sporadic.HNOddCore.LCheckInputs
public import Certificates.Certificate2086

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native

theorem lift_cert : liftChecksO (hnsData.orbit ()) = true :=
  Certificates.certificate2086

end CFSG.Sporadic.HNOddCore.Native

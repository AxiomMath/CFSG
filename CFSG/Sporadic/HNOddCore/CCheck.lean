
module

public import CFSG.Sporadic.HNOddCore.CCheckBase

public import CFSG.Sporadic.HNSchreier.ThreeCheck
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public import Certificates.Certificate2083

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native

theorem c_cert : cChecksO (hnsData.orbit ()) = true :=
  Certificates.certificate2083

end CFSG.Sporadic.HNOddCore.Native

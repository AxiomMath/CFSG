module

public import CFSG.Sporadic.ONOddCore.LiftCheck
public meta import CFSG.Sporadic.ONOddCore.LiftCheck
public import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs
public import CFSG.Sporadic.ONOddCore.LiftGraphInputs
public import Certificates.Certificate2122

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native

theorem lift_res_cert : liftResOK (wordArrs Data.MWords) = true :=
  Certificates.certificate2122.1

theorem lift_graph_cert :
    localCert.records.all (fun r => r.lifts.all liftGraphOK) = true :=
  Certificates.certificate2122.2

end CFSG.Sporadic.ONOddCore

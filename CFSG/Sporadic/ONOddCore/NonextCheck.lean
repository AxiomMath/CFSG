module

public import CFSG.Sporadic.ONOddCore.NonextPayload
public import CFSG.Sporadic.ONOddCore.LiftHomCheck
public import CFSG.Sporadic.Schreier.ONCheckR3E
public meta import CFSG.Sporadic.ONOddCore.NonextPayload
public meta import CFSG.Sporadic.ONOddCore.LiftHomCheck
public meta import CFSG.Sporadic.Schreier.ONCheckR3E
public import CFSG.Sporadic.ONOddCore.NonextCheckInputs
public import Certificates.Certificate2125

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

theorem nonext_cert :
    nonextOK (wordArrs Data.MWords) flatLifts nonextCert nonextWords = true :=
  Certificates.certificate2125

end CFSG.Sporadic.ONOddCore

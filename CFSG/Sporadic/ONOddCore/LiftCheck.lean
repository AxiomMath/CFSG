module

public import CFSG.Sporadic.ONOddCore.LiftPayload
public import CFSG.Sporadic.ONOddCore.QuotOuterCheck
public import CFSG.Sporadic.Schreier.ONCheckAux
public meta import CFSG.Sporadic.ONOddCore.LiftPayload
public meta import CFSG.Sporadic.ONOddCore.QuotOuterCheck
public meta import CFSG.Sporadic.Schreier.ONCheckAux
public import CFSG.Sporadic.ONOddCore.LiftCheckInputs
public import Certificates.Certificate2120

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ON.Native

theorem cand_cert : candidatesCheck (wordArrs Data.MWords) = true :=
  Certificates.certificate2120

end CFSG.Sporadic.ONOddCore

module

public import CFSG.Sporadic.Schreier.ONCheckChain
public meta import CFSG.Sporadic.Schreier.ONCheckChain
public import CFSG.Sporadic.ONOddCore.MinusCheckInputs
public import Certificates.Certificate2124

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

theorem minus_cert :
    minusOK qonStrongArrs CFSG.ONSchreier.Data.baseList.toArray sigmaArr = true :=
  Certificates.certificate2124

end CFSG.Sporadic.ONOddCore

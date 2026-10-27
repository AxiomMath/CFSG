module

public import CFSG.Sporadic.ONOddCore.LocalAutPayload
public import CFSG.Sporadic.ONOddCore.SigmaTriple
public import CFSG.Sporadic.ONOddCore.GraphDefs
public import CFSG.Sporadic.Schreier.ONCheckSmallAux
public meta import CFSG.Sporadic.ONOddCore.LocalAutPayload
public meta import CFSG.Sporadic.ONOddCore.SigmaTriple
public meta import CFSG.Sporadic.ONOddCore.GraphDefs
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux
public import CFSG.Sporadic.ONOddCore.QuotOuterCheckInputs
public import Certificates.Certificate2127

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native

theorem quot_cert : quotCheck (indexOf m120Enum.tabs) = true :=
  Certificates.certificate2127

end CFSG.Sporadic.ONOddCore

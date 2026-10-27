module

public import Certificates.Data.CFSGNative.Fi23.Classes
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public meta import Certificates.Data.CFSGNative.Fi23.Classes
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer
public import CFSG.Sporadic.FischerOddCore.Fi23WitCheckInputs
public import Certificates.Certificate2075

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

theorem fi23Wit_certificate : fi23WitChecks (orbitData ()) = true :=
  Certificates.certificate2075

end CFSG.Sporadic.FischerOddCore

module

public import Certificates.Data.CFSGNative.Fi23.Classes
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public meta import Certificates.Data.CFSGNative.Fi23.Classes
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer
public import CFSG.Sporadic.FischerOddCore.Fi23UniqCheckInputs
public import Certificates.Certificate2074

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

theorem fi23Uniq_certificate : fi23UniqOK (orbitData ()) = true :=
  Certificates.certificate2074.1

theorem fi23Trip_certificate : fi23TripOK (orbitData ()) = true :=
  Certificates.certificate2074.2

end CFSG.Sporadic.FischerOddCore


module

public import CFSG.Sporadic.Schreier.Co3OrbitZCheckBase

public import CFSG.Sporadic.Schreier.Co3Cert
public import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public import CFSG.Sporadic.Schreier.Co3OrbitZCheckInputs
public import Certificates.Certificate2157

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

theorem co3OrbitZ_check :
    translatesOK co3OrigArrs co3IzNat co3OrbitZ.1 co3OrbitZ.2.1 co3OrbitZ.2.2 = true ∧
    keysSortedOK co3OrbitZ.1 = true ∧ co3OrbitZ.1.size = 170775 :=
  Certificates.certificate2157

end CFSG.Sporadic.Schreier.Co3

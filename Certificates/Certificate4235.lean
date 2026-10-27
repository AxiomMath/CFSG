module

public import Certificates.Data.D4HexGeoCheck
public import Certificates.Data.D4HexBase
import Certificates.Kernel.S63K.G4235

public section

namespace Certificates

open CertificateChecks

theorem certificate4235 : CFSG.D4Hex.d4GeoCheck CFSG.D4Hex.lineTab CFSG.D4Hex.lay0 CFSG.D4Hex.permArrs = true := KernelS63.G4235.c4235

end Certificates


module


import Certificates.Kernel.VecCert.Co1Final
public import CFSG.Sporadic.Co1.Module.OrbitsInputs
public import Certificates.Certificate3024Base

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module in
theorem certificate10074 :
    vOrbitOK 24 98280 dat.colsA dat.colsB (orbitOf 2 98280) = true := KernelVec.Co1.orbit_v₂

end Certificates

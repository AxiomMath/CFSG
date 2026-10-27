module

public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
public import Certificates.Kernel.SporSch.Co2S.ItBind
public import Certificates.Certificate3115
public import Certificates.Certificate3117

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Schreier.Co3 in
theorem certificate2054 : (itList.length = 140)
    ∧ (orbitRecordOK itList 1024650 (co3KeySearch aArrs itList 1024650) = true) := KernelSporSch.Co2t.facts

end Certificates

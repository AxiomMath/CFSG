module

public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
import Certificates.Kernel.SporSch.Co2M.OrbZ

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Schreier.Co3 in
theorem certificate2055 : (izList.length = 284)
    ∧ (orbitRecordOK izList 56925 (co3KeySearch aArrs izList 56925) = true) :=
  ⟨KernelSporSch.Co2M.iz_length, KernelSporSch.Co2M.record⟩

end Certificates

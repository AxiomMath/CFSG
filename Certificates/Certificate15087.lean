module

public import Certificates.Data.HeRCentCheck
import Certificates.Kernel.LocalComp.HeRCheck

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelLC.HeR in
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.ComponentClassification.AS81.HePres.Native in
theorem certificate15087 :
    (heGenArrsOK = true)
    ∧ (heRInvolOK = true)
    ∧ (heRWitOK = true)
    ∧ (heRCentOK = true)
    ∧ (rawChainOK 8330 (heRStrong.extract 0 2) heRStrong heRChainBaseArr heRChainWords 1 = true)
    ∧ ((rawOrbitSizes 8330 heRStrong heRChainBaseArr).prod = 80640)
    ∧ (heRStrong.size = 9)
    ∧ ((eqA 8330 heRStrong[0]! heRChainOrig[0]! && eqA 8330 heRStrong[1]! heRChainOrig[1]!) = true) :=
  ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, chain, order, facts.2.2.2.2.1,
    facts.2.2.2.2.2.2⟩

end Certificates

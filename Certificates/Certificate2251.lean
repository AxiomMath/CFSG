module

public import CFSG.Sporadic.Schreier.RuCheckIsoInputs
import Certificates.Kernel.SporSch.Ru.Sig2251T

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.SmallF2.Native in
theorem certificate2251 : isInvA 4060 ruSigmaA (invCand 4060 ruSigmaA) = true ∧
    (∀ i < 4060, ruSigmaA[ruA0A[i]!]! =
        ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).alpha ruSigmaA[i]! ∧
      ruSigmaA[ruA1A[i]!]! = ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).beta ruSigmaA[i]!) := KernelSporSch.RuSig.facts_proved

end Certificates

module

public import CFSG.Sporadic.Schreier.RuMixInputs
import Certificates.Kernel.SporSch.Ru.Mix

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native in
theorem certificate15501 : eqA 4060 (powA 4060 (ruMixA 13) 7) (idA 4060) = true ∧
    eqA 4060 (ruMixA 13) (idA 4060) = false ∧
    eqA 4060 (powA 4060 (ruMixA 5) 13) (idA 4060) = true ∧
    eqA 4060 (ruMixA 5) (idA 4060) = false := KernelSporSch.RuMix.c15501

end Certificates

module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporRuGoodInputs
import Certificates.Kernel.SporSch.Ru.Good4096

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.RuPairs in
open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem certificate4096 : (isInvA 4060 ruBCA (ruInv ruBCA) = true ∧
          isInvA 4060 ruJGensA[0]! (ruInv ruJGensA[0]!) = true ∧
          eqA 4060 (powA 4060 ruBCA 3) (idA 4060) = true ∧ eqA 4060 ruBCA (idA 4060) = false ∧
          eqA 4060 (powA 4060 ruCCA 5) (idA 4060) = true ∧ eqA 4060 ruCCA (idA 4060) = false ∧
          eqA 4060 (compA 4060 ruXCA ruXCA) (idA 4060) = false ∧
          eqA 4060 (compA 4060 ruJGensA[0]! ruCCA) (compA 4060 ruCCA ruJGensA[0]!) = false)
    ∧ (isInvA 4060 ruKGensA[0]! (ruInv ruKGensA[0]!) = true ∧
          eqA 4060 (powA 4060 ruNs1A 3) (idA 4060) = true ∧ eqA 4060 ruNs1A (idA 4060) = false ∧
          isInvA 4060 ruCNA (ruInv ruCNA) = true ∧
          eqA 4060 (powA 4060 ruCNA 7) (idA 4060) = true ∧ eqA 4060 ruCNA (idA 4060) = false ∧
          eqA 4060 (compA 4060 ruXNA ruXNA) (idA 4060) = false ∧
          eqA 4060 (compA 4060 ruKGensA[0]! ruCNA) (compA 4060 ruCNA ruKGensA[0]!) = false) := KernelSporSch.RuGd.facts

end Certificates

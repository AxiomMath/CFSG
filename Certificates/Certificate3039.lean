
module


public import CFSG.Monster.B.Fischer.PinnedChainInputs
import Certificates.Kernel.Sporadic.Fi22.C3039

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer in
theorem certificate3039 : (∀ j < 19, isInvA 3510 fi22StrongArrs[j]! fi22StrongInvs[j]! = true) ∧
      (∀ k < 2, isInvA 3510 (fi22ChainGen k) (invCand 3510 (fi22ChainGen k)) = true) ∧
      (∀ k < 2, eqA 3510 fi22StrongArrs[k]! (fi22ChainGen k) = true) ∧
      (∀ j < 19, 2 ≤ j → CFSG.Monster.B.Co2.Native.lettersOK j (fi22Derivation j) = true ∧
        eqA 3510 fi22StrongArrs[j]!
          (CFSG.Monster.B.Co2.Native.wordA 3510 fi22StrongArrs fi22StrongInvs (fi22Derivation j)) = true) ∧
      fi22ChainDerivations.length = 17 := KernelSpor.Fi22C3039.certificate3039_of

end Certificates

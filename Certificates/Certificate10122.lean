module

public import CFSG.YGroups.Y443.Native.Parabolic2Words
import Certificates.Kernel.KDense.Y443

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 in
theorem certificate10122 :
    wordLin (rhoWord ++ rhoWord) = 1
    ∧ (∀ s ∈ rhoGens, wordLin (Lw s ++ rhoWord) = wordLin (rhoWord ++ Lw (armSwapL s)))
    ∧ wordLin (omegaWord ++ mWord) = wordLin (rhoWord ++ omegaWord)
    ∧ wordLin (zmWord ++ qWord) = wordLin (qWord ++ tWord) :=
  CertificateChecks.KernelKDense.Y443.c10122

end Certificates

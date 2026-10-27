module

public import CFSG.YGroups.Y443.Native.BrayWords
import Certificates.Kernel.KDense.Y443.Bray

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 in
theorem certificate10111 :
    wordLin (omegaWord ++ kWord) = wordLin (eWord ++ omegaWord)
    ∧ wordLin gWord = wordLin (xWord ++ kWord ++ xWord ++ kWord)
    ∧ wordLin (xWord ++ gWord) = wordLin (gWord ++ xWord)
    ∧ wordLin (tWord ++ gWord) ≠ wordLin (gWord ++ tWord)
    ∧ wordLin (tWord ++ gWord) ≠ wordLin (gWord ++ tWord ++ xWord) :=
  CertificateChecks.KernelKDense.Y443.c10111

end Certificates

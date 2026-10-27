module

public import CFSG.YGroups.Y443.Native.CoverFactsWords
import Certificates.Kernel.KDense.Y443
public import CFSG.YGroups.Y443.Native.Align

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 in
theorem certificate10112 :
    wordLin (EdgeNoncomm.pairsWord EdgeNoncomm.nP ++ omegaWord) = wordLin (omegaWord ++ coverPHat)
    ∧ wordLin (powL 3 coverPHat) = 1
    ∧ wordLin (coverQ ++ omegaWord) = wordLin (omegaWord ++ coverQHat)
    ∧ wordLin (coverQHat ++ coverPHat ++ coverWy) = wordLin (coverWy ++ tWord) :=
  CertificateChecks.KernelKDense.Y443.c10112

end Certificates

module

public import CFSG.YGroups.Y443.Native.Swap13Word
import Certificates.Kernel.KDense.Y443
public import CFSG.YGroups.Y443.Native.Parabolic2Words

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 in
theorem certificate10124 :
    wordLin (tWord ++ swap13Word) = wordLin (swap13Word ++ tWord)
    ∧ wordLin (mtmWord ++ swap13Word) = wordLin (swap13Word ++ zmWord) :=
  CertificateChecks.KernelKDense.Y443.c10124

end Certificates

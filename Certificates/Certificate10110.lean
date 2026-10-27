module

public import CFSG.YGroups.Y443.Native.Align
import Certificates.Kernel.KDense.Y443

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 in
theorem certificate10110 : wordLin (wcWord ++ omegaWord) = wordLin (omegaWord ++ tWord) :=
  CertificateChecks.KernelKDense.Y443.c10110

end Certificates

module

public import CFSG.RankThree.Native.ONSevenArrays
import Certificates.Kernel.ONSeven.C8135

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native in
theorem certificate8135 : (

    onSevenTransCheck 0 = true ∧ onSevenTransCheck 1 = true ∧ onSevenTransCheck 2 = true ∧
      onSevenTransCheck 3 = true ∧ onSevenTransCheck 4 = true
)
    ∧ (onSevenKernelCheck = true) :=
  KernelSpor.ONS.facts8135

end Certificates

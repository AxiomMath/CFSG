module

public import CFSG.RankThree.Native.ONSevenArrays
import Certificates.Kernel.ONSeven.B8134F

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native in
theorem certificate8134 : (onSevenBoundCheck 0 (onSevenConjArr 0) 49 28 false = true)
    ∧ (onSevenBoundCheck 1 (onSevenConjArr 1) 49 28 false = true)
    ∧ (onSevenBoundCheck 2 (onSevenConjArr 2) 49 28 false = true)
    ∧ (onSevenBoundCheck 3 (onSevenConjArr 3) 49 1 true = true)
    ∧ (onSevenBoundCheck 4 (onSevenConjArr 4) 49 1 true = true) :=
  KernelSpor.ONS.facts8134

end Certificates

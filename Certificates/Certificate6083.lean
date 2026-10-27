module

public import CFSG.Monster.Existence.TwoPoint.ThCheck
import Certificates.Kernel.KDenseP.TwoPoint.Th

public section

namespace Certificates

open CFSG.Monster.AxisCount CFSG.Monster.Existence in
theorem certificate6083 : (∀ i ∈ List.range 8, wordLin (thWU[i]! ++ thWV[i]!) = 1) ∧ wordLin thWAB3 = 1 ∧
    wordLin thWAB ≠ 1 ∧ wordLin thWS7 = 1 ∧ wordLin thWU[5]! ≠ 1 :=
  CertificateChecks.KernelKDenseP.TwoPoint.c6083

end Certificates

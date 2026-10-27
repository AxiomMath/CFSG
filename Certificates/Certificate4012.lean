module

public import CFSG.Sporadic.J4.QT2LocVLClassNative
import Certificates.Kernel.J4Q.C4012

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2 in
theorem certificate4012 : vlAll.size = 149 ∧ (∀ g < 149, vlAll[g]!.size = 16) ∧
    (∀ g < 149, ∃ r ∈ vlRepIdx, ∃ c < 6720, vlConjEq r g c = true ∧
      eqRows (mulRows vlCx[c]! vlCxInv[c]!) idRows = true) ∧
    chkNamed = true :=
  KernelJ4Q.c4012

end Certificates

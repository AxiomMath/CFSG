module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7InstInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7W
import Certificates.Kernel.J4Q.C4111

public section

namespace Certificates

open CertificateChecks.KernelJ4Q

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.B7 in
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2.B7 in
theorem certificate4111 : chkB7V (wR b7TWord) b7G0 387 = true ∧
    survP (wR b7TWord) b7G0 CFSG.Sporadic.J4.Native.rootV ∧
    survOrb (wR b7TWord) b7G0 5 15180 ∧
    survOrb (wR b7TWord) b7G0 6 28336 ∧
    baseP (wR b7TWord) ∧
    chkCross (vRows (wR b7TWord)) (b7ExplicitWords.map wR).toArray = true ∧
    chkCross (b7ExplicitWords.map wR).toArray (vRows (wR b7TWord)) = true :=
  c4111

end Certificates

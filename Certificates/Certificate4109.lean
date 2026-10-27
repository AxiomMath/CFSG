module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Native
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2AInputs
import Certificates.Kernel.J4Q.D2A9
import Certificates.Kernel.J4Q.D2A8

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 in
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 CFSG.QuasithinUnique.A5.Dec2 in
theorem certificate4109 : (CFSG.QuasithinUnique.A5.Dec2.chkAll a941Words (wR a941q) = true)
    ∧ (CFSG.QuasithinUnique.A5.Dec2.chkAll a85Words (wR a85q) = true) := ⟨KernelJ4Q.a9_all, KernelJ4Q.a8_all⟩

end Certificates

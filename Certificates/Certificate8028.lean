module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.ON
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8028 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.ON, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := KernelLocalQT.on_elem

end Certificates

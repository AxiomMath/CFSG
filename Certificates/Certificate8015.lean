module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.Fi23
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8015 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Fi23, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := KernelLocalQT.fi23_elem

end Certificates

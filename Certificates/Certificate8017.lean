module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.HN
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8017 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.HN, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := KernelLocalQT.hn_elem

end Certificates

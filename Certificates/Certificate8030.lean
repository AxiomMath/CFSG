module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.Suz
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8030 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Suz, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := KernelLocalQT.suz_elem

end Certificates

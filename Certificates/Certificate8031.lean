module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.Th
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8031 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Th, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := KernelLocalQT.th_elem

end Certificates

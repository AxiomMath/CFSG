module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.Co1
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8011 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Co1, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := KernelLocalQT.co1_elem

end Certificates

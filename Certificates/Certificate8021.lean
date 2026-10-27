module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.J3
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8021 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.J3, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 3 := KernelLocalQT.j3_elem

end Certificates

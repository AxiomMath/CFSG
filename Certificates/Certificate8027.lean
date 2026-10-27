module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.McL
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8027 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.McL, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4 := KernelLocalQT.mcl_elem

end Certificates

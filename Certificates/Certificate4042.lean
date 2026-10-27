module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.Nine
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate4042 :
    (∃ E : Subgroup CFSG.Blueprint.NativeSporadic.J2, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2) ∧
      (∃ E : Subgroup CFSG.Blueprint.NativeSporadic.HS, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2) := ⟨KernelLocalQT.j2_nine, KernelLocalQT.hs_nine⟩

end Certificates

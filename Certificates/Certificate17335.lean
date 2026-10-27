module

public import Mathlib.GroupTheory.OrderOfElement
import Certificates.Kernel.Sporadic.Fi22.Small17335G
public import CFSG.Monster.B.Fischer.PinnedChainBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer (fi22P) in
theorem certificate17335 : (∃ u ∈ fi22P, orderOf u = 7 ∧ Nat.card {w : Fin 3510 // u w = w} = 3) ∧
    (∃ u ∈ fi22P, orderOf u = 11 ∧ Nat.card {w : Fin 3510 // u w = w} = 1) ∧
    (∃ u ∈ fi22P, orderOf u = 13 ∧ Nat.card {w : Fin 3510 // u w = w} = 0) :=
  KernelSpor.Small17335.facts

end Certificates

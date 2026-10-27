module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.J3LocalDet
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open CFSG.Open in
theorem certificate8022 :
    ∃ (K : Subgroup CFSG.Blueprint.NativeSporadic.J3) (_ : Group.IsPerfect K) (Q : Sylow 3 K)
      (x y : K) (h k : CFSG.Blueprint.NativeSporadic.J3),
      Nat.card K = 360 ∧ IsElemAbelian 3 (Q : Subgroup K) ∧
      Nat.card (Q : Subgroup K) = 3 ^ 2 ∧
      h ∈ Subgroup.normalizer (K : Set CFSG.Blueprint.NativeSporadic.J3) ∧
      Subgroup.closure ({x, y} : Set K) = Q ∧
      h * x * h⁻¹ = (x : CFSG.Blueprint.NativeSporadic.J3) ^ 2 *
        (y : CFSG.Blueprint.NativeSporadic.J3) ^ 1 ∧
      h * y * h⁻¹ = (x : CFSG.Blueprint.NativeSporadic.J3) ^ 1 *
        (y : CFSG.Blueprint.NativeSporadic.J3) ^ 0 ∧
      (∀ g ∈ K, Commute k g) ∧ orderOf k = 3 ∧ Subgroup.zpowers k ⊓ K = ⊥ := KernelLocalQT.j3_local_det

end Certificates

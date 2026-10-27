module

public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.GroupTheory.PCore.Defs
import Certificates.Kernel.PermCent.K55107F

public section

namespace Certificates

open CFSG.GH74.KGroups.U33 Subgroup in
theorem certificate55107 : Nat.card QP.originalSubgroup = 6048 ∧
    centralizer (QP.originalSubgroup : Set (Equiv.Perm (Fin 28))) = ⊥ ∧
    ∃ u : Equiv.Perm (Fin 28), u ^ 2 = 1 ∧ u ∉ QP.originalSubgroup ∧
      (∀ p ∈ QP.originalSubgroup, u * p * u⁻¹ ∈ QP.originalSubgroup) ∧
      ∀ t ∈ QP.originalSubgroup ⊔ zpowers u, orderOf t = 2 →
        CFSG.oddCore ↥(QP.originalSubgroup ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 28)))) = ⊥ :=
  CertificateChecks.KernelPermCent.U33.facts

end Certificates

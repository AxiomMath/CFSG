
module


public import CFSG.GH74.KGroups.L34TablesInputs
import Certificates.Kernel.PermCent.KG5124Glue

public section

open CFSG.Certificates.Kernel.PkCV.KGrp

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.L34 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate5124 : (x0 ^ 2 = 1 ∧ x0 ≠ 1 ∧ x0 ∈ QP.originalSubgroup)
    ∧ (∀ y ∈ QP.originalSubgroup, y ^ 2 = 1 → y ≠ 1 →
      ∃ g ∈ QP.originalSubgroup, g * x0 * g⁻¹ = y)
    ∧ (QP.originalSubgroup ≤ QA.originalSubgroup)
    ∧ (Nat.card ↥(QP.originalSubgroup ⊓
      Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42)))) = 64)
    ∧ (Nat.card ↥(QA.originalSubgroup ⊓
      Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42)))) = 768)
    ∧ (∀ σ ∈ QA.originalSubgroup, (∀ q ∈ QP.originalSubgroup ⊓
      Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42))), σ * q = q * σ) → σ ^ 2 = 1) :=
  ⟨K5124.x0_facts, K5124.one_class', K5124.P_le_A', K5124.card_CP', K5124.card_CA',
    K5124.cent_sq'⟩

end Certificates

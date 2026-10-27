module

public import CFSG.GH74.KGroups.Sz8DInputs
import Certificates.Kernel.PermCent.K5129Glue

public section

open CFSG.Certificates.Kernel.PkCV.KGrp.K5129

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.Sz8D in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8 in
theorem certificate5129 : (∀ s ∈ QS.originalSubgroup, s cpt = cpt)
    ∧ (∀ i : Fin 65, (∀ s ∈ QS.originalSubgroup, s i = i) → i = cpt)
    ∧ (∀ j, ys j ∈ QS.originalSubgroup ⊓
      Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))))
    ∧ (ys 0 ≠ 1)
    ∧ (∀ κ : Equiv.Perm (Fin 65) → Equiv.Perm (Fin 65) → ZMod 2,
      (∀ x ∈ QS.originalSubgroup, ∀ x' ∈ QS.originalSubgroup,
        ∀ y ∈ QS.originalSubgroup ⊓
          Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
          κ (x * x') y = κ x y + κ x' y) →
      (∀ x ∈ QS.originalSubgroup,
        ∀ y ∈ QS.originalSubgroup ⊓
          Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
        ∀ y' ∈ QS.originalSubgroup ⊓
          Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
          κ x (y * y') = κ x y + κ x y') →
      (∀ w ∈ QS.originalSubgroup ⊓
          Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
        ∀ y ∈ QS.originalSubgroup ⊓
          Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))), κ w y = 0) →
      (∀ x ∈ QS.originalSubgroup, κ x (x ^ 2) = 0) →
      (∀ s ∈ QS.originalSubgroup,
        ∀ t ∈ QS.originalSubgroup ⊓
          Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
          κ (tt * s * tt⁻¹) (tt * t * tt⁻¹) = κ s t) →
      ∀ σ : Equiv.Perm (Fin 65), σ ∈ QA.originalSubgroup → σ cpt = cpt →
        σ ∉ QP.originalSubgroup →
      (∀ s ∈ QS.originalSubgroup,
        ∀ t ∈ QS.originalSubgroup ⊓
          Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
          κ (σ * s * σ⁻¹) (σ * t * σ⁻¹) = κ s t) →
      ∀ s ∈ QS.originalSubgroup,
        ∀ t ∈ QS.originalSubgroup ⊓
          Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))), κ s t = 0) :=
  ⟨S_fix_k, fix_unique_k, ys_k, ys0_k, hfin_k⟩

end Certificates

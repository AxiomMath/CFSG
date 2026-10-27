module

public import CFSG.Assembly.Defs
public import Mathlib.Algebra.Group.Commutator

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

theorem commutator_sup_le_of_isElemAbelian {X : Type*} [Group X] {p : ℕ} {E N : Subgroup X}
    (hE : IsElemAbelian p E) (hEN : E ≤ Subgroup.normalizer (N : Set X)) :
    ⁅(⊤ : Subgroup ↥(E ⊔ N)), (⊤ : Subgroup ↥(E ⊔ N))⁆ ≤ N.subgroupOf (E ⊔ N) := by
  haveI hEab : IsMulCommutative E := hE.1
  have hNM : (N.subgroupOf (E ⊔ N)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    exact sup_le hEN Subgroup.le_normalizer
  haveI := hNM
  have hsup : N.subgroupOf (E ⊔ N) ⊔ E.subgroupOf (E ⊔ N) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_right le_sup_left, sup_comm, Subgroup.subgroupOf_self]
  have hcomm :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      (N := N.subgroupOf (E ⊔ N)) (H := E.subgroupOf (E ⊔ N)) hsup inferInstance
  simpa only [_root_.commutator] using hcomm

end CFSG.StandardType

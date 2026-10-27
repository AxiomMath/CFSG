module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# Normality transported from a derived-subgroup model

A subgroup of a normal subgroup is ambient-normal when, after transport by
an isomorphism, it is the derived subgroup of the model group.
-/

namespace CFSG.GorensteinWalter

universe u v

/-- If `E ≤ L ◁ Q` and the internal copy of `E` maps to the commutator
subgroup under an equivalence `L ≃ M`, then `E ◁ Q`. -/
public theorem normal_of_subgroupOf_map_eq_commutator
    {Q : Type u} [Group Q]
    (L E : Subgroup Q) (hLnormal : L.Normal) (hEL : E ≤ L)
    {M : Type v} [Group M] (e : L ≃* M)
    (hmap : (E.subgroupOf L).map e.toMonoidHom = commutator M) :
    E.Normal := by
  let EL : Subgroup L := E.subgroupOf L
  have hcommMap : (commutator L).map e.toMonoidHom = commutator M := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have hELcomm : EL = commutator L := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact hmap.trans hcommMap.symm
  let : EL.Characteristic := by
    rw [hELcomm]
    infer_instance
  let : L.Normal := hLnormal
  have hnormalMap : (EL.map L.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hrecover : EL.map L.subtype = E := by
    dsimp [EL]
    exact Subgroup.map_subgroupOf_eq_of_le hEL
  rw [hrecover] at hnormalMap
  exact hnormalMap

end CFSG.GorensteinWalter

module

public import CFSG.Sporadic.SuzRecog.Q3ARonan
public import CFSG.Sporadic.SuzRecog.Q3ATits
public import CFSG.Sporadic.SuzRecog.ModelGroups

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.Q3A

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Co1Patterson

@[expose] def layer
    (hN : NrhoBound) : IndexLayer where
  vtx := vtx
  exists_vtx := exists_vtx hN
  smul_vtx := fun ha _ hi => smul_vtx hN ha hi
  adj_vtx_iff := fun hi hj => adj_vtx_iff hN hi hj
  vtx_zero := vtx_zero

theorem nrhoBound :
    NrhoBound :=
  ModelGroups.card_Nrho1.ge

theorem exists_titsData_a4 :
    ∃ D : TitsDataBy a4Graph triT ↥suzM (Fin 2),
      D.v = v0 ∧ D.w = vtx TitsCheck.iv1 ∧
      D.Xv = ModelGroups.Nrho1.subgroupOf suzM ∧ D.Xe = ModelGroups.pairStab.subgroupOf suzM ∧
      D.Xt 0 = (ModelGroups.triStab (ModelGroups.rho2 * Model.rho1)).subgroupOf suzM ∧
      D.Xt 1 = (closure {ModelGroups.s1, ModelGroups.s2}).subgroupOf suzM := by
  have hN : NrhoBound := nrhoBound
  obtain ⟨-, -, h1, -, -, hadj01, -⟩ := titsCheck_parts
  have hadj : a4Graph.Adj v0 (vtx TitsCheck.iv1) := by
    rw [← vtx_zero]
    exact (adj_vtx_iff hN (by norm_num) h1).2 hadj01
  exact exists_titsData (layer hN) (a4_preconnected hN) (a4_triangulable hN)
    fun y hy => exists_stab_of_adj hN hadj hy

end CFSG.Sporadic.SuzRecog.Q3A

module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.H13.NQCoreAnotherMaxLocal

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

theorem isPerfect_of_surjective {Q Q' : Type*} [Group Q] [Group Q'] (f : Q →* Q')
    (hf : Function.Surjective f) (h : Group.IsPerfect Q) : Group.IsPerfect Q' := by
  rw [Group.isPerfect_def, eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ commutator Q := h.commutator_eq_top ▸ mem_top x
  have h1 := Subgroup.mem_map_of_mem f hx
  rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr hf, ← _root_.commutator_def] at h1

variable {G : Type} [Group G] [Finite G]

end CFSG.Quasithin.H13.NQCore

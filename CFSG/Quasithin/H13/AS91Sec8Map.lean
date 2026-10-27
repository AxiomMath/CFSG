module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.Quasithin.H13.AS91

variable {G : Type*} [Group G] {Gb : Type*} [Group Gb]

theorem map_subgroupOf_eq_iff {A : Subgroup G} {B : Subgroup Gb} (e : ↥A ≃* ↥B)
    (S : Subgroup G) (T : Subgroup Gb) :
    (S.subgroupOf A).map e.toMonoidHom = T.subgroupOf B ↔
      ∀ g : ↥A, (g : G) ∈ S ↔ ((e g : ↥B) : Gb) ∈ T := by
  constructor
  · intro h g
    have h1 : g ∈ S.subgroupOf A ↔ e g ∈ (S.subgroupOf A).map e.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      simp
    rw [h] at h1
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro h
    ext c
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := h (e.symm c)
    rw [MulEquiv.apply_symm_apply] at this
    exact this

end CFSG.Quasithin.H13.AS91

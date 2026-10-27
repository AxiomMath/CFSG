module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem exists_isComponent_centralizer_of_mulEquiv {T T' : Type*} [Group T] [Group T']
    (e : T ≃* T') {u : T} {Q : Subgroup T}
    (hQ : CFSG.Assembly.IsComponentOf Q (centralizer ({u} : Set T))) :
    ∃ K : Subgroup (centralizer ({e u} : Set T')), CFSG.IsComponent K := by
  have hQ' := (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
  have hc : (centralizer ({u} : Set T)).map e.toMonoidHom = centralizer ({e u} : Set T') := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
      rw [mem_centralizer_singleton_iff]
      change e y * e u = e u * e y
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [mem_centralizer_singleton_iff] at hx
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hx]
  let c : centralizer ({u} : Set T) ≃* centralizer ({e u} : Set T') :=
    ((centralizer {u}).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hc)
  exact ⟨_, CFSG.LocalCores.isComponent_map_mulEquiv c hQ'⟩

end CFSG.LocalAnalysis

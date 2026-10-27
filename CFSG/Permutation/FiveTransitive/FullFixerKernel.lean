module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG

namespace FiveTransitive.FullFixerKernel

open MulAction FixedNormalizerAction

theorem kernel_eq_inside
    {G X : Type*} [Group G] [MulAction G X] (s : Set X) :
    (toPermHom (Normalizer (fixingSubgroup G s))
      (Fixed (X := X) (fixingSubgroup G s))).ker = Inside (fixingSubgroup G s) := by
  let H := fixingSubgroup G s
  ext g
  constructor
  · intro hg
    change g.val ∈ H
    apply (mem_fixingSubgroup_iff G).mpr
    intro x hx
    have hxF : x ∈ Fixed (X := X) H := by
      rw [fixed_eq]
      intro h
      exact (mem_fixingSubgroup_iff G).mp h.property x hx
    have he := Equiv.congr_fun (show toPermHom (Normalizer H) (Fixed (X := X) H) g = 1 from hg) ⟨x,hxF⟩
    exact congrArg Subtype.val he
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have hx : x.val ∈ fixedPoints H X := by rw [← fixed_eq H]; exact x.property
    exact mem_fixedPoints.mp hx ⟨g.val,hg⟩

theorem restricted_kernel_isPGroup
    {G X : Type*} [Group G] [MulAction G X] {p : ℕ}
    (s : Set X) (hH : IsPGroup p (fixingSubgroup G s))
    (C : Subgroup (Normalizer (fixingSubgroup G s))) :
    IsPGroup p ((toPermHom (Normalizer (fixingSubgroup G s))
      (Fixed (X := X) (fixingSubgroup G s))).comp C.subtype).ker := by
  have hk : IsPGroup p (toPermHom (Normalizer (fixingSubgroup G s))
      (Fixed (X := X) (fixingSubgroup G s))).ker := by
    rw [kernel_eq_inside]
    exact hH.comap_subtype
  exact hk.comap_of_injective C.subtype C.subtype_injective

end FiveTransitive.FullFixerKernel

end CFSG

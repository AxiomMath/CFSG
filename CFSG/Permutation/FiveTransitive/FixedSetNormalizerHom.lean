module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG

namespace FiveTransitive.FixedSetNormalizerHom

open MulAction FixedSetNormalizerPerm

@[expose] def fixedPermHom
    (G X : Type*) [Group G] [MulAction G X] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) →* Equiv.Perm (fixedPoints Q X) where
  toFun a := fixedPerm G X Q a.val a.property
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact one_smul G x.val
  map_mul' a b := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact mul_smul (a : G) (b : G) x.val

@[simp] theorem fixedPermHom_apply_val
    (G X : Type*) [Group G] [MulAction G X] (Q : Subgroup G)
    (a : Subgroup.normalizer (Q : Set G)) (x : fixedPoints Q X) :
    ((fixedPermHom G X Q) a x).val = (a : G) • x.val := rfl

theorem mem_ker_iff
    (G X : Type*) [Group G] [MulAction G X] (Q : Subgroup G)
    (a : Subgroup.normalizer (Q : Set G)) :
    a ∈ (fixedPermHom G X Q).ker ↔ ∀ x ∈ fixedPoints Q X, (a : G) • x = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha x hx
    exact congrArg Subtype.val (DFunLike.congr_fun ha (⟨x,hx⟩ : fixedPoints Q X))
  · intro ha
    apply Equiv.ext
    intro x
    exact Subtype.ext (ha x.val x.property)

end FiveTransitive.FixedSetNormalizerHom

end CFSG

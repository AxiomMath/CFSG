module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG

namespace FiveTransitive.FixedSetNormalizerPerm

open MulAction

theorem smul_mem_fixedPoints
    (G X : Type*) [Group G] [MulAction G X] (Q : Subgroup G)
    (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G))
    {x : X} (hx : x ∈ fixedPoints Q X) : a • x ∈ fixedPoints Q X := by
  rw [mem_fixedPoints]
  intro q
  have hconj : a⁻¹ * (q : G) * a ∈ Q :=
    (Subgroup.mem_normalizer_iff''.mp ha (q : G)).mp q.property
  have hfix := mem_fixedPoints.mp hx ⟨a⁻¹ * (q : G) * a, hconj⟩
  change (a⁻¹ * (q : G) * a) • x = x at hfix
  have h := congrArg (fun y : X => a • y) hfix
  change (q : G) • (a • x) = a • x
  simpa only [mul_smul, smul_inv_smul] using h

@[expose] def fixedPerm
    (G X : Type*) [Group G] [MulAction G X] (Q : Subgroup G)
    (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)) : Equiv.Perm (fixedPoints Q X) where
  toFun x := ⟨a • x.val, smul_mem_fixedPoints G X Q a ha x.property⟩
  invFun x := ⟨a⁻¹ • x.val, smul_mem_fixedPoints G X Q a⁻¹
    ((Subgroup.normalizer (Q : Set G)).inv_mem ha) x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

@[simp] theorem fixedPerm_apply_val
    (G X : Type*) [Group G] [MulAction G X] (Q : Subgroup G)
    (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)) (x : fixedPoints Q X) :
    (fixedPerm G X Q a ha x).val = a • x.val := rfl

@[simp] theorem fixedPerm_pow_apply_val
    (G X : Type*) [Group G] [MulAction G X] (Q : Subgroup G)
    (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G))
    (n : ℕ) (x : fixedPoints Q X) :
    ((fixedPerm G X Q a ha ^ n) x).val = a ^ n • x.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, fixedPerm_apply_val, ih, pow_succ', mul_smul]

end FiveTransitive.FixedSetNormalizerPerm

end CFSG

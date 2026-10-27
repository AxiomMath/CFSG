module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugation actions on subgroups

This file provides a small piece of infrastructure: if a subgroup `A ≤ G` normalizes a subgroup
`K ≤ G`, then the group `↥A` acts on the group `↥K` by conjugation.

This is useful for applying coprime-action lemmas (e.g. invariant Hall subgroups) inside a subgroup
of `G` which is stable under conjugation by `A`.
-/

namespace Subgroup

section ConjAction

variable {G : Type*} [Group G]

/-- `A` normalizes `K`, i.e. `A` is contained in the normalizer of `K`. -/
public class Normalizes (A K : Subgroup G) : Prop where
  le_normalizer : A ≤ normalizer K

/-- If `A ≤ normalizer K`, then `↥A` acts on `↥K` by conjugation inside `G`. -/
@[reducible, expose]
public def conjMulDistribMulActionOfLeNormalizer (A K : Subgroup G)
    (hAK : A ≤ normalizer K) :
    MulDistribMulAction (↥A) (↥K) :=
  let smulFun : (↥A) → (↥K) → (↥K) :=
    fun a k =>
      ⟨(a : G) * (k : G) * (a : G)⁻¹,
        (mem_normalizer_iff.mp (hAK a.property) (k : G)).1 k.property⟩
  { smul := smulFun
    one_smul := by
      intro k
      change smulFun (1 : (↥A)) k = k
      apply Subtype.ext
      simp [smulFun]
    mul_smul := by
      intro a b k
      change smulFun (a * b) k = smulFun a (smulFun b k)
      apply Subtype.ext
      simp [smulFun, mul_assoc]
    smul_mul := by
      intro a x y
      change smulFun a (x * y) = smulFun a x * smulFun a y
      apply Subtype.ext
      simp [smulFun, mul_assoc]
    smul_one := by
      intro a
      change smulFun a (1 : (↥K)) = 1
      apply Subtype.ext
      simp [smulFun] }

public theorem conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
    (A K : Subgroup G) (hAK : A ≤ normalizer K) (a : A) (k : K) :
    (((conjMulDistribMulActionOfLeNormalizer A K hAK).smul a k : K) : G) =
      (a : G) * (k : G) * (a : G)⁻¹ := rfl

-- When K is normal, every A normalizes it
public instance (priority := high) (A K : Subgroup G) [K.Normal] : Normalizes A K :=
  ⟨le_normalizer_of_normal (H := K)⟩

-- From a Fact hypothesis
public instance (A K : Subgroup G) [Fact (A ≤ normalizer K)] : Normalizes A K :=
  ⟨Fact.out⟩

-- The global MulDistribMulAction instance
@[reducible]
public instance (A K : Subgroup G) [Normalizes A K] : MulDistribMulAction (↥A) (↥K) :=
  conjMulDistribMulActionOfLeNormalizer A K Normalizes.le_normalizer

@[simp] public theorem conjMulDistribMulActionOfLeNormalizer_smul_coe
    (A K : Subgroup G) [Normalizes A K] (a : A) (k : K) :
    ((a • k : K) : G) = (a : G) * (k : G) * (a : G)⁻¹ := by
  calc
    ((a • k : K) : G) = ((conjMulDistribMulActionOfLeNormalizer A K Normalizes.le_normalizer).smul a k : G) := rfl
    _ = (a : G) * (k : G) * (a : G)⁻¹ := rfl

@[simp] public theorem conjMulDistribMulActionOfNormal_smul_coe
    (A K : Subgroup G) [K.Normal] (a : A) (k : K) :
    ((a • k : K) : G) = (a : G) * (k : G) * (a : G)⁻¹ :=
  conjMulDistribMulActionOfLeNormalizer_smul_coe A K a k

end ConjAction

end Subgroup

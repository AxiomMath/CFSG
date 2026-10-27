module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def subgroupProduct (first second : Subgroup GroupType) : Set GroupType :=
  (first : Set GroupType) * (second : Set GroupType)

@[expose] def subgroupProductHom (first second : Subgroup GroupType) : first × second → subgroupProduct first second :=
  fun pair => ⟨pair.1.val * pair.2.val, ⟨pair.1.val, pair.1.property, pair.2.val, pair.2.property, rfl⟩⟩

theorem subgroup_product_hom_surjective (first second : Subgroup GroupType) :
    Function.Surjective (subgroupProductHom first second) := by
  rintro ⟨element, firstElement, first_member, secondElement, second_member, product_eq⟩
  exact ⟨(⟨firstElement, first_member⟩, ⟨secondElement, second_member⟩), Subtype.ext product_eq⟩

@[expose] noncomputable def subgroupProductFiberEquiv (first second : Subgroup GroupType)
    (element : subgroupProduct first second) :
    {pair : first × second // subgroupProductHom first second pair = element} ≃
      (first ⊓ second : Subgroup GroupType) := by
  classical
  let base := Classical.choose (subgroup_product_hom_surjective first second element)
  have base_eq := Classical.choose_spec (subgroup_product_hom_surjective first second element)
  have base_product : base.1.val * base.2.val = element.val := congrArg Subtype.val base_eq
  refine
    { toFun := fun pair => ⟨base.1.val⁻¹ * pair.val.1.val, ?_⟩
      invFun := fun internal => ⟨(⟨base.1.val * internal.val, first.mul_mem base.1.property internal.property.1⟩,
        ⟨internal.val⁻¹ * base.2.val, second.mul_mem (second.inv_mem internal.property.2) base.2.property⟩), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨first.mul_mem (first.inv_mem base.1.property) pair.val.1.property, ?_⟩
    have pair_product : pair.val.1.val * pair.val.2.val = element.val :=
      congrArg Subtype.val pair.property
    have difference : base.1.val⁻¹ * pair.val.1.val = base.2.val * pair.val.2.val⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).mpr
      rw [mul_assoc, pair_product, ← base_product, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [difference]
    exact second.mul_mem base.2.property (second.inv_mem pair.val.2.property)
  · apply Subtype.ext
    change (base.1.val * internal.val) * (internal.val⁻¹ * base.2.val) = element.val
    rw [mul_assoc, ← mul_assoc internal.val, mul_inv_cancel, one_mul]
    exact base_product
  · intro pair
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact mul_inv_cancel_left _ _
    · apply Subtype.ext
      have pair_product : pair.val.1.val * pair.val.2.val = element.val :=
        congrArg Subtype.val pair.property
      change (base.1.val⁻¹ * pair.val.1.val)⁻¹ * base.2.val = pair.val.2.val
      rw [mul_inv_rev, inv_inv, mul_assoc, base_product, ← pair_product, inv_mul_cancel_left]
  · intro internal
    apply Subtype.ext
    exact inv_mul_cancel_left _ _

theorem subgroup_product_cardinality (first second : Subgroup GroupType) :
    Nat.card first * Nat.card second =
      Nat.card (subgroupProduct first second) * Nat.card (first ⊓ second : Subgroup GroupType) := by
  let equivalence := (Equiv.sigmaFiberEquiv (subgroupProductHom first second)).symm.trans
    ((Equiv.sigmaCongrRight (subgroupProductFiberEquiv first second)).trans
      (Equiv.sigmaEquivProd _ _))
  simpa only [Nat.card_prod] using Nat.card_congr equivalence

theorem subgroup_product_eq_univ_iff (first second : Subgroup GroupType) :
    subgroupProduct first second = Set.univ ↔
      ∀ element : GroupType, ∃ firstElement ∈ first, ∃ secondElement ∈ second,
        firstElement * secondElement = element := by
  constructor
  · intro whole element
    have member : element ∈ subgroupProduct first second := by rw [whole]; trivial
    exact member
  · intro decomposable
    exact Set.eq_univ_of_forall decomposable

end CFSG.SignalizerFunctor.Helpers

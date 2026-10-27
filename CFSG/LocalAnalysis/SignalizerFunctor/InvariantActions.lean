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

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable [MulDistribMulAction ActorType GroupType]

abbrev invariantSubgroupAction (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) : MulDistribMulAction ActorType subgroup where
  smul actorElement element := ⟨actorElement • element.val,
    invariant actorElement element.val element.property⟩
  one_smul element := by
    apply Subtype.ext
    exact one_smul ActorType element.val
  mul_smul first second element := by
    apply Subtype.ext
    exact mul_smul first second element.val
  smul_one actorElement := by
    apply Subtype.ext
    exact smul_one actorElement
  smul_mul actorElement first second := by
    apply Subtype.ext
    exact MulDistribMulAction.smul_mul actorElement first.val second.val

abbrev invariantQuotientAction (subgroup : Subgroup GroupType) [subgroup.Normal]
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) : MulDistribMulAction ActorType (GroupType ⧸ subgroup) := by
  let _quotientAction : MulAction.QuotientAction ActorType subgroup := ⟨by
    intro actorElement first second member
    simpa only [MulDistribMulAction.smul_mul, smul_inv'] using
      invariant actorElement (first⁻¹ * second) member⟩
  refine { (inferInstance : MulAction ActorType (GroupType ⧸ subgroup)) with
    smul_one := ?_, smul_mul := ?_ }
  · intro actorElement
    change actorElement • ((1 : GroupType) : GroupType ⧸ subgroup) = 1
    rw [MulAction.Quotient.smul_coe, smul_one]
    rfl
  · intro actorElement first second
    induction first using QuotientGroup.induction_on with
    | H first =>
      induction second using QuotientGroup.induction_on with
      | H second =>
        change actorElement • ((first * second : GroupType) : GroupType ⧸ subgroup) = _
        rw [MulAction.Quotient.smul_coe, MulDistribMulAction.smul_mul,
          MulAction.Quotient.smul_coe, MulAction.Quotient.smul_coe]
        rfl

theorem invariant_quotient_equivariant (subgroup : Subgroup GroupType) [subgroup.Normal]
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) :
    let _action := invariantQuotientAction subgroup invariant
    ∀ actorElement : ActorType, ∀ element : GroupType,
      QuotientGroup.mk' subgroup (actorElement • element) =
        actorElement • QuotientGroup.mk' subgroup element := by
  let _action := invariantQuotientAction subgroup invariant
  change ∀ actorElement : ActorType, ∀ element : GroupType,
    QuotientGroup.mk' subgroup (actorElement • element) =
      actorElement • QuotientGroup.mk' subgroup element
  intro actorElement element
  rfl

theorem invariant_subgroup_fixed_points_le (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) (actorSubgroup : Subgroup ActorType) :
    let _action := invariantSubgroupAction subgroup invariant
    (FixedPoints.subgroup actorSubgroup subgroup).map subgroup.subtype ≤
      FixedPoints.subgroup actorSubgroup GroupType := by
  let _action := invariantSubgroupAction subgroup invariant
  change (FixedPoints.subgroup actorSubgroup subgroup).map subgroup.subtype ≤
    FixedPoints.subgroup actorSubgroup GroupType
  rintro element ⟨representative, fixed, rfl⟩ actorElement
  exact congrArg (fun internal : subgroup => (internal : GroupType))
    (fixed actorElement)

theorem invariant_subgroup_fixed_points_map (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) :
    let _action := invariantSubgroupAction subgroup invariant
    (FixedPoints.subgroup ActorType subgroup).map subgroup.subtype =
      subgroup ⊓ FixedPoints.subgroup ActorType GroupType := by
  let _action := invariantSubgroupAction subgroup invariant
  change (FixedPoints.subgroup ActorType subgroup).map subgroup.subtype =
    subgroup ⊓ FixedPoints.subgroup ActorType GroupType
  ext element
  constructor
  · rintro ⟨representative, fixed, rfl⟩
    refine ⟨representative.property, ?_⟩
    intro actorElement
    exact congrArg (fun internal : subgroup => (internal : GroupType)) (fixed actorElement)
  · rintro ⟨member, fixed⟩
    refine ⟨⟨element, member⟩, ?_, rfl⟩
    intro actorElement
    exact Subtype.ext (fixed actorElement)

end CFSG.SignalizerFunctor.Helpers

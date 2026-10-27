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

universe actorUniverse groupUniverse targetUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable {TargetType : Type targetUniverse} [Group TargetType]
variable [MulDistribMulAction ActorType GroupType]
variable [MulDistribMulAction ActorType TargetType]

theorem fixed_point_lifts (prime : ℕ) (prime_prime : prime.Prime)
    (actor_pgroup : IsPGroup prime ActorType) (homomorphism : GroupType →* TargetType)
    (surjective : Function.Surjective homomorphism)
    (equivariant : ∀ (actorElement : ActorType) (groupElement : GroupType),
      homomorphism (actorElement • groupElement) = actorElement • homomorphism groupElement)
    (kernel_coprime : Nat.Coprime prime (Nat.card homomorphism.ker))
    (targetElement : TargetType) (fixed : ∀ actorElement : ActorType,
      actorElement • targetElement = targetElement) :
    ∃ groupElement : GroupType, homomorphism groupElement = targetElement ∧
      ∀ actorElement : ActorType, actorElement • groupElement = groupElement := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let fibre : SubMulAction ActorType GroupType :=
    ⟨{element | homomorphism element = targetElement}, by
      intro actorElement groupElement member
      change homomorphism (actorElement • groupElement) = targetElement
      rw [equivariant, member, fixed]⟩
  have fibre_card : Nat.card fibre = Nat.card homomorphism.ker :=
    Nat.card_congr (homomorphism.fiberEquivKerOfSurjective surjective targetElement)
  have fibre_prime : ¬ prime ∣ Nat.card fibre := by
    rw [fibre_card]
    exact prime_prime.coprime_iff_not_dvd.mp kernel_coprime
  obtain ⟨representative, representative_fixed⟩ :=
    actor_pgroup.nonempty_fixed_point_of_prime_not_dvd_card fibre fibre_prime
  refine ⟨representative, representative.property, ?_⟩
  intro actorElement
  exact congrArg (fun element : fibre => (element : GroupType))
    (representative_fixed actorElement)

theorem fixed_subgroup_map (prime : ℕ) (prime_prime : prime.Prime)
    (actor_pgroup : IsPGroup prime ActorType) (homomorphism : GroupType →* TargetType)
    (surjective : Function.Surjective homomorphism)
    (equivariant : ∀ (actorElement : ActorType) (groupElement : GroupType),
      homomorphism (actorElement • groupElement) = actorElement • homomorphism groupElement)
    (kernel_coprime : Nat.Coprime prime (Nat.card homomorphism.ker)) :
    (FixedPoints.subgroup ActorType GroupType).map homomorphism =
      FixedPoints.subgroup ActorType TargetType := by
  ext targetElement
  constructor
  · rintro ⟨representative, representative_fixed, rfl⟩
    intro actorElement
    rw [← equivariant, representative_fixed actorElement]
  · intro fixed
    obtain ⟨representative, representative_maps, representative_fixed⟩ :=
      fixed_point_lifts prime prime_prime actor_pgroup homomorphism surjective
        equivariant kernel_coprime targetElement fixed
    exact ⟨representative, representative_fixed, representative_maps⟩

end CFSG.SignalizerFunctor.Helpers

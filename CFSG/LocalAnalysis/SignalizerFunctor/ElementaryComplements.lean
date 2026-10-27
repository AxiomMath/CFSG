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

universe groupUniverse moduleUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem additive_zmod_isCompl_exists
    (prime : ℕ) (prime_prime : prime.Prime)
    (ModuleType : Type moduleUniverse) [AddCommGroup ModuleType]
    [Module (ZMod prime) ModuleType] (subgroup : AddSubgroup ModuleType) :
    ∃ complement : AddSubgroup ModuleType, IsCompl subgroup complement := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let correspondence := AddSubgroup.toZModSubmodule prime (M := ModuleType)
  obtain ⟨complement, complementary⟩ := (correspondence subgroup).exists_isCompl
  refine ⟨correspondence.symm complement, ?_⟩
  have transported := correspondence.symm.isCompl complementary
  simpa only [OrderIso.symm_apply_apply] using transported

theorem elementary_abelian_isCompl_exists
    (prime : ℕ) (prime_prime : prime.Prime)
    (GroupType : Type groupUniverse) [CommGroup GroupType]
    (exponent : ∀ element : GroupType, element ^ prime = 1)
    (subgroup : Subgroup GroupType) :
    ∃ complement : Subgroup GroupType, IsCompl subgroup complement := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let : NeZero prime := ⟨prime_prime.ne_zero⟩
  have additive_exponent : ∀ element : Additive GroupType, prime • element = 0 := by
    intro element
    exact exponent element.toMul
  let _module : Module (ZMod prime) (Additive GroupType) :=
    AddCommMonoid.zmodModule additive_exponent
  obtain ⟨complement, complementary⟩ := additive_zmod_isCompl_exists prime prime_prime
    (Additive GroupType) subgroup.toAddSubgroup
  have multiplicativeComplement :=
    (Subgroup.toAddSubgroup (G := GroupType)).symm.isCompl complementary
  refine ⟨Subgroup.toAddSubgroup.symm complement, ?_⟩
  simpa only [OrderIso.symm_apply_apply] using multiplicativeComplement

theorem isComplement'_of_isCompl_commutative
    {GroupType : Type groupUniverse} [CommGroup GroupType]
    {subgroup complement : Subgroup GroupType} (complementary : IsCompl subgroup complement) :
    subgroup.IsComplement' complement := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ complementary.disjoint
  apply Set.eq_univ_iff_forall.mpr
  intro element
  have member : element ∈ subgroup ⊔ complement := by
    rw [complementary.sup_eq_top]
    trivial
  obtain ⟨first, first_member, second, second_member, product⟩ :=
    Subgroup.mem_sup.mp member
  exact ⟨first, first_member, second, second_member, product⟩

theorem elementary_abelian_complement_exists
    (prime : ℕ) (prime_prime : prime.Prime)
    (GroupType : Type groupUniverse) [CommGroup GroupType]
    (exponent : ∀ element : GroupType, element ^ prime = 1)
    (subgroup : Subgroup GroupType) :
    ∃ complement : Subgroup GroupType, subgroup.IsComplement' complement := by
  obtain ⟨complement, complementary⟩ :=
    elementary_abelian_isCompl_exists prime prime_prime GroupType exponent subgroup
  exact ⟨complement, isComplement'_of_isCompl_commutative complementary⟩

end CFSG.SignalizerFunctor.Helpers

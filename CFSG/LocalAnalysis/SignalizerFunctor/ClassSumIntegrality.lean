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
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

universe groupUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]

@[expose] noncomputable def representationClassSum (representation : Representation ℂ GroupType VectorType)
    (elements : Finset GroupType) : Module.End ℂ VectorType := ∑ element ∈ elements, representation element

omit [Finite GroupType] in
theorem finite_group_orbit_lattice_invariant (representation : Representation ℂ GroupType VectorType)
    (vector : VectorType) (element : GroupType) :
    ∀ value ∈ Submodule.span ℤ (Set.range (fun conjugator : GroupType => representation conjugator vector)),
      representation element value ∈ Submodule.span ℤ (Set.range (fun conjugator : GroupType => representation conjugator vector)) := by
  intro value member
  induction member using Submodule.span_induction with
  | mem value member =>
    obtain ⟨conjugator, rfl⟩ := member
    have product : representation element (representation conjugator vector) = representation (element * conjugator) vector := by
      rw [map_mul]
      rfl
    rw [product]
    exact Submodule.subset_span ⟨element * conjugator, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add first second _ _ first_member second_member =>
    rw [map_add]
    exact Submodule.add_mem _ first_member second_member
  | smul scalar value _ value_member =>
    rw [map_zsmul]
    exact Submodule.smul_mem _ scalar value_member

theorem finite_group_scalar_class_sum_integral (representation : Representation ℂ GroupType VectorType)
    [Nontrivial VectorType] (elements : Finset GroupType) (scalar : ℂ)
    (scalar_sum : representationClassSum representation elements = scalar • (1 : Module.End ℂ VectorType)) :
    IsIntegral ℤ scalar := by
  classical
  obtain ⟨vector, vector_ne⟩ := exists_ne (0 : VectorType)
  let lattice := Submodule.span ℤ (Set.range (fun conjugator : GroupType => representation conjugator vector))
  have vector_lattice : vector ∈ lattice := by
    have generated : representation 1 vector ∈ lattice := Submodule.subset_span ⟨1, rfl⟩
    simpa only [map_one, Module.End.one_apply] using generated
  have lattice_nontrivial : lattice ≠ ⊥ := fun trivial => vector_ne (by
    rw [trivial] at vector_lattice
    exact vector_lattice)
  have finitely_generated : lattice.FG := Submodule.fg_span (Set.finite_range _)
  apply isIntegral_of_smul_mem_submodule lattice lattice_nontrivial finitely_generated scalar
  intro value member
  have sum_member : representationClassSum representation elements value ∈ lattice := by
    change (∑ element ∈ elements, representation element) value ∈ lattice
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem lattice (fun element _ => finite_group_orbit_lattice_invariant representation vector element value member)
  rwa [scalar_sum, LinearMap.smul_apply, Module.End.one_apply] at sum_member

omit [Finite GroupType] in
theorem invariant_class_sum_commutes (representation : Representation ℂ GroupType VectorType)
    (elements : Finset GroupType)
    (invariant : ∀ conjugator : GroupType, ∀ element ∈ elements, conjugator * element * conjugator⁻¹ ∈ elements)
    (conjugator : GroupType) :
    representationClassSum representation elements * representation conjugator =
      representation conjugator * representationClassSum representation elements := by
  classical
  unfold representationClassSum
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_bij (fun element _ => conjugator⁻¹ * element * conjugator)
  · intro element member
    simpa only [inv_inv] using invariant conjugator⁻¹ element member
  · intro first _ second _ equal
    have normalized : (MulAut.conj conjugator⁻¹) first = (MulAut.conj conjugator⁻¹) second := by
      simpa only [MulAut.conj_apply, inv_inv] using equal
    exact (MulAut.conj conjugator⁻¹).injective normalized
  · intro element member
    refine ⟨conjugator * element * conjugator⁻¹, invariant conjugator element member, ?_⟩
    group
  · intro element _
    rw [← map_mul, ← map_mul]
    congr 1
    group

omit [Finite GroupType] in
theorem irreducible_class_sum_scalar [FiniteDimensional ℂ VectorType]
    (representation : Representation ℂ GroupType VectorType) [representation.IsIrreducible]
    (elements : Finset GroupType)
    (invariant : ∀ conjugator : GroupType, ∀ element ∈ elements, conjugator * element * conjugator⁻¹ ∈ elements) :
    ∃ scalar : ℂ, representationClassSum representation elements = scalar • (1 : Module.End ℂ VectorType) := by
  let intertwiner : representation.IntertwiningMap representation :=
    { toLinearMap := representationClassSum representation elements
      isIntertwining' := invariant_class_sum_commutes representation elements invariant }
  obtain ⟨scalar, equal⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := representation) |>.surjective intertwiner
  exact ⟨scalar, (congrArg (fun candidate : representation.IntertwiningMap representation => candidate.toLinearMap) equal).symm⟩

theorem irreducible_class_sum_central_character_integral [FiniteDimensional ℂ VectorType] [Nontrivial VectorType]
    (representation : Representation ℂ GroupType VectorType) [representation.IsIrreducible]
    (elements : Finset GroupType)
    (invariant : ∀ conjugator : GroupType, ∀ element ∈ elements, conjugator * element * conjugator⁻¹ ∈ elements)
    (element : GroupType) (same_character : ∀ selected ∈ elements, representation.character selected = representation.character element) :
    IsIntegral ℤ ((elements.card : ℂ) * representation.character element / (Module.finrank ℂ VectorType : ℂ)) := by
  obtain ⟨scalar, scalar_equal⟩ := irreducible_class_sum_scalar representation elements invariant
  have scalar_integral := finite_group_scalar_class_sum_integral representation elements scalar scalar_equal
  have trace_equal := congrArg (LinearMap.trace ℂ VectorType) scalar_equal
  have trace_sum : (LinearMap.trace ℂ VectorType) (representationClassSum representation elements) =
      (elements.card : ℂ) * representation.character element := by
    unfold representationClassSum
    rw [map_sum]
    calc
      _ = ∑ _selected ∈ elements, representation.character element := Finset.sum_congr rfl same_character
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [trace_sum, map_smul, LinearMap.trace_one, smul_eq_mul] at trace_equal
  have rank_ne : (Module.finrank ℂ VectorType : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := VectorType)).ne'
  have ratio : (elements.card : ℂ) * representation.character element / (Module.finrank ℂ VectorType : ℂ) = scalar :=
    (div_eq_iff rank_ne).mpr trace_equal
  rwa [ratio]

end CFSG.SignalizerFunctor.Helpers

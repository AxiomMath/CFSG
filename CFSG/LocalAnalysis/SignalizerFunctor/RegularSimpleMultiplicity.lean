module

public import CFSG.LocalAnalysis.SignalizerFunctor.SimpleGroupAlgebraHomDimensions
public import CFSG.LocalAnalysis.SignalizerFunctor.RegularCharacterValues
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

universe groupUniverse indexUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem finite_group_algebra_submodule_finiteDimensional
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (submodule : Submodule (MonoidAlgebra ℂ GroupType) (MonoidAlgebra ℂ GroupType)) :
    FiniteDimensional ℂ submodule := by
  let : Fintype GroupType := Fintype.ofFinite GroupType
  let : FiniteDimensional ℂ (MonoidAlgebra ℂ GroupType) := Module.Finite.of_basis (MonoidAlgebra.basis GroupType ℂ)
  exact Module.Finite.equiv ((Submodule.restrictScalarsEquiv ℂ (MonoidAlgebra ℂ GroupType)
    (MonoidAlgebra ℂ GroupType) submodule).restrictScalars ℂ)

theorem regular_simple_summand_multiplicity
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    {IndexType : Type indexUniverse} [Fintype IndexType] [DecidableEq IndexType]
    (summands : IndexType → Submodule (MonoidAlgebra ℂ GroupType) (MonoidAlgebra ℂ GroupType))
    (internal : DirectSum.IsInternal summands)
    (simple : ∀ index, IsSimpleModule (MonoidAlgebra ℂ GroupType) (summands index))
    (selected : IndexType) :
    Nat.card {index : IndexType // Nonempty ((summands index) ≃ₗ[MonoidAlgebra ℂ GroupType] (summands selected))} =
      Module.finrank ℂ (summands selected) := by
  classical
  let : ∀ index, FiniteDimensional ℂ (summands index) := fun index => finite_group_algebra_submodule_finiteDimensional (summands index)
  let : ∀ index, IsSimpleModule (MonoidAlgebra ℂ GroupType) (summands index) := simple
  have dimensions := group_algebra_hom_finrank_decomposition summands internal (summands selected)
  rw [group_algebra_regular_hom_finrank] at dimensions
  have indicator : ∀ index,
      Module.finrank ℂ ((summands index) →ₗ[MonoidAlgebra ℂ GroupType] (summands selected)) =
        if Nonempty ((summands index) ≃ₗ[MonoidAlgebra ℂ GroupType] (summands selected)) then 1 else 0 :=
    fun index => simple_group_algebra_hom_finrank (summands index) (summands selected)
  simp_rw [indicator] at dimensions
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [Finset.card_filter] using dimensions.symm

noncomputable def simpleSummandSetoid
    {GroupType : Type groupUniverse} [Group GroupType]
    {IndexType : Type indexUniverse}
    (summands : IndexType → Submodule (MonoidAlgebra ℂ GroupType) (MonoidAlgebra ℂ GroupType)) :
    Setoid IndexType :=
  { r := fun first second => Nonempty ((summands first) ≃ₗ[MonoidAlgebra ℂ GroupType] (summands second))
    iseqv :=
      { refl := fun _index => ⟨LinearEquiv.refl _ _⟩
        symm := fun ⟨equivalence⟩ => ⟨equivalence.symm⟩
        trans := fun ⟨first⟩ ⟨second⟩ => ⟨first.trans second⟩ } }

theorem regular_simple_character_identity
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    {IndexType : Type indexUniverse} [Fintype IndexType] [DecidableEq IndexType]
    (summands : IndexType → Submodule (MonoidAlgebra ℂ GroupType) (MonoidAlgebra ℂ GroupType))
    (internal : DirectSum.IsInternal summands)
    (simple : ∀ index, IsSimpleModule (MonoidAlgebra ℂ GroupType) (summands index))
    (character_sum : ∀ element : GroupType, (Representation.leftRegular ℂ GroupType).character element =
      ∑ index, (Representation.ofModule' (k := ℂ) (G := GroupType) (summands index)).character element)
    (element : GroupType)
    [Fintype (Quotient (simpleSummandSetoid summands))] :
    (Representation.leftRegular ℂ GroupType).character element =
      ∑ summandClass : Quotient (simpleSummandSetoid summands),
        (Module.finrank ℂ (summands summandClass.out) : ℂ) *
          (Representation.ofModule' (k := ℂ) (G := GroupType) (summands summandClass.out)).character element := by
  classical
  let classes := Quotient (simpleSummandSetoid summands)
  let projection : IndexType → classes := Quotient.mk _
  let character : IndexType → ℂ := fun index =>
    (Representation.ofModule' (k := ℂ) (G := GroupType) (summands index)).character element
  rw [character_sum, ← Fintype.sum_fiberwise projection character]
  apply Finset.sum_congr rfl
  intro summandClass _member
  have fiber_equiv : ∀ index : IndexType, projection index = summandClass ↔
      Nonempty ((summands index) ≃ₗ[MonoidAlgebra ℂ GroupType] (summands summandClass.out)) := by
    intro index
    conv_lhs => rw [← Quotient.out_eq summandClass]
    rw [Quotient.eq]
    rfl
  have fiber_card : Fintype.card {index : IndexType // projection index = summandClass} =
      Module.finrank ℂ (summands summandClass.out) := by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight fiber_equiv), ← Nat.card_eq_fintype_card]
    exact regular_simple_summand_multiplicity summands internal simple summandClass.out
  have fiber_character : ∀ index : {index : IndexType // projection index = summandClass},
      character index.val = character summandClass.out := by
    intro index
    obtain ⟨equivalence⟩ := (fiber_equiv index.val).mp index.property
    exact equivalent_group_algebra_characters equivalence element
  change (∑ index : {index : IndexType // projection index = summandClass}, character index.val) = _
  rw [Finset.sum_eq_card_nsmul (fun index _member => fiber_character index), nsmul_eq_mul, Finset.card_univ, fiber_card]

end CFSG.SignalizerFunctor.Helpers

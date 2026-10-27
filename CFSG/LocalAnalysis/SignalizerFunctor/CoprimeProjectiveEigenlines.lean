module

public import Mathlib.LinearAlgebra.Semisimple
public import CFSG.LocalAnalysis.SignalizerFunctor.ProjectiveLinearActions
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

universe fieldUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]

theorem coprime_order_linear_semisimple
    (prime : ℕ) [CharP FieldType prime]
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (exponent : ℕ) (coprime : ¬prime ∣ exponent) (power_one : automorphism ^ exponent = 1) :
    Module.End.IsSemisimple automorphism.toLinearMap := by
  have separable := Polynomial.separable_X_pow_sub_C' prime exponent (1 : FieldType) coprime one_ne_zero
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero separable.squarefree
  have operator_power : automorphism.toLinearMap ^ exponent = 1 := by
    have mapped := congrArg
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := FieldType) (M := VectorType)) power_one
    simpa only [map_pow, map_one, LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using mapped
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, operator_power, sub_self]

theorem projective_eigenline_distinct_of_independent
    (first second : VectorType) (first_nonzero : first ≠ 0) (second_nonzero : second ≠ 0)
    (independent : LinearIndependent FieldType ![first, second]) :
    Projectivization.mk FieldType first first_nonzero ≠
      Projectivization.mk FieldType second second_nonzero := by
  intro equal
  obtain ⟨scalar, scalar_eq⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp equal.symm
  exact (LinearIndependent.pair_iff' first_nonzero).mp independent scalar scalar_eq

theorem semisimple_projective_distinct_eigenlines [IsAlgClosed FieldType]
    [FiniteDimensional FieldType VectorType] [Nontrivial VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (semisimple : Module.End.IsSemisimple automorphism.toLinearMap)
    (projective_nonidentity : projectiveLinearAction automorphism ≠ 1) :
    ∃ first second : VectorType, ∃ first_scalar second_scalar : FieldType,
      first ≠ 0 ∧ second ≠ 0 ∧ LinearIndependent FieldType ![first, second] ∧
      automorphism first = first_scalar • first ∧ automorphism second = second_scalar • second ∧
      first_scalar ≠ second_scalar := by
  classical
  obtain ⟨first_scalar, first_eigenvalue⟩ := Module.End.exists_eigenvalue automorphism.toLinearMap
  obtain ⟨first, first_eigenvector⟩ := first_eigenvalue.exists_hasEigenvector
  have first_eigen : automorphism first = first_scalar • first := first_eigenvector.apply_eq_smul
  let first_line := Submodule.span FieldType ({first} : Set VectorType)
  have first_line_dimension : Module.finrank FieldType first_line = 1 :=
    finrank_span_singleton first_eigenvector.2
  have first_line_invariant : first_line ∈ Module.End.invtSubmodule automorphism.toLinearMap := by
    intro vector member
    obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp member
    change automorphism (scalar • first) ∈ first_line
    rw [map_smul, first_eigen, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  obtain ⟨complement, complement_invariant, complementary⟩ :=
    Module.End.isSemisimple_iff.mp semisimple first_line first_line_invariant
  have complement_dimension : Module.finrank FieldType complement = 1 := by
    have dimensions := Submodule.finrank_sup_add_finrank_inf_eq first_line complement
    rw [complementary.sup_eq_top, complementary.inf_eq_bot, finrank_top, finrank_bot,
      dimension, first_line_dimension] at dimensions
    omega
  let _nontrivial : Nontrivial complement :=
    Module.nontrivial_of_finrank_pos (by rw [complement_dimension]; omega)
  obtain ⟨second_scalar, second_eigenvalue⟩ := Module.End.exists_eigenvalue
    (automorphism.toLinearMap.restrict complement_invariant)
  obtain ⟨second, second_eigenvector⟩ := second_eigenvalue.exists_hasEigenvector
  have second_nonzero : second.val ≠ 0 := by
    intro zero
    exact second_eigenvector.2 (Subtype.ext zero)
  have independent : LinearIndependent FieldType ![first, second.val] := by
    apply (LinearIndependent.pair_iff' first_eigenvector.2).mpr
    intro scalar equal
    have second_first : second.val ∈ first_line := equal ▸ first_line.smul_mem scalar (Submodule.subset_span rfl)
    have second_intersection : second.val ∈ first_line ⊓ complement := ⟨second_first, second.property⟩
    rw [complementary.inf_eq_bot, Submodule.mem_bot] at second_intersection
    exact second_nonzero second_intersection
  have second_eigen : automorphism second.val = second_scalar • second.val :=
    congrArg Subtype.val second_eigenvector.apply_eq_smul
  have scalar_distinct : first_scalar ≠ second_scalar := by
    intro equal
    apply projective_nonidentity
    have span_top := independent.span_eq_top_of_card_eq_finrank (by simpa using dimension.symm)
    have agrees : Set.EqOn automorphism.toLinearMap
        (fun vector : VectorType => (first_scalar • (1 : Module.End FieldType VectorType)) vector)
        (Set.range ![first, second.val]) := by
      rintro vector ⟨index, rfl⟩
      fin_cases index
      · exact first_eigen
      · change automorphism second.val = first_scalar • second.val
        rwa [equal]
    have all_eigen : ∀ vector : VectorType, automorphism vector = first_scalar • vector := by
      intro vector
      exact LinearMap.eqOn_span (f := automorphism.toLinearMap)
        (g := first_scalar • (1 : Module.End FieldType VectorType)) agrees
        (x := vector) (by rw [span_top]; exact Submodule.mem_top)
    apply Equiv.ext
    intro point
    induction point using Projectivization.ind with
    | h vector nonzero =>
      exact (projective_linear_fixed_iff_eigenvector automorphism vector nonzero).mpr
        ⟨first_scalar, all_eigen vector⟩
  exact ⟨first, second.val, first_scalar, second_scalar, first_eigenvector.2, second_nonzero,
    independent, first_eigenvector.apply_eq_smul, second_eigen, scalar_distinct⟩

end CFSG.SignalizerFunctor.Helpers

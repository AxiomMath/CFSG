module

public import CFSG.LocalAnalysis.SignalizerFunctor.ClassSumIntegrality
public import CFSG.LocalAnalysis.SignalizerFunctor.RegularCharacterValues
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.Coalgebra.CoassocSimps

public section

universe groupUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem trivial_irreducible_degree_one
    {GroupType : Type groupUniverse} [Group GroupType]
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    [FiniteDimensional ℂ VectorType]
    (representation : Representation ℂ GroupType VectorType) [representation.IsIrreducible]
    (trivial_action : ∀ element, representation element = 1) : Module.finrank ℂ VectorType = 1 := by
  let equivalence : representation.IntertwiningMap representation ≃ₗ[ℂ] Module.End ℂ VectorType :=
    { toFun := fun hom => hom.toLinearMap
      invFun := fun operator =>
        { toLinearMap := operator
          isIntertwining' := fun element => by rw [trivial_action]; rfl }
      left_inv := fun hom => rfl
      right_inv := fun operator => rfl
      map_add' := fun first second => rfl
      map_smul' := fun scalar operator => rfl }
  have dimension := equivalence.finrank_eq
  rw [Representation.IsIrreducible.finrank_intertwiningMap_self representation,
    Module.finrank_linearMap ℂ ℂ] at dimension
  nlinarith

theorem nontrivial_irreducible_character_sum_zero
    {GroupType : Type groupUniverse} [Group GroupType] [Fintype GroupType]
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    [FiniteDimensional ℂ VectorType] [Nontrivial VectorType]
    (representation : Representation ℂ GroupType VectorType) [representation.IsIrreducible]
    (nontrivial_action : ¬∀ element, representation element = 1) : ∑ element, representation.character element = 0 := by
  classical
  obtain ⟨scalar, equal⟩ := irreducible_class_sum_scalar representation Finset.univ
    (fun _conjugator _element _member => Finset.mem_univ _)
  have norm_equal : representation.norm = scalar • (1 : Module.End ℂ VectorType) := equal
  have scalar_zero : scalar = 0 := by
    by_contra nonzero
    apply nontrivial_action
    intro element
    have commute := representation.norm_comp_self element
    rw [norm_equal] at commute
    have scalar_equal : scalar • representation element = scalar • (1 : Module.End ℂ VectorType) := by
      change scalar • LinearMap.id ∘ₗ representation element = scalar • LinearMap.id at commute
      simpa only [LinearMap.smul_comp, LinearMap.id_comp, Module.End.one_eq_id] using commute
    exact (smul_right_injective _ nonzero) scalar_equal
  have norm_zero : representation.norm = 0 := by rw [norm_equal, scalar_zero, zero_smul]
  have trace_zero := congrArg (LinearMap.trace ℂ VectorType) norm_zero
  simpa only [Representation.norm, map_sum, map_zero, Representation.character] using trace_zero

theorem finite_group_regular_character_sum
    {GroupType : Type groupUniverse} [Group GroupType] [Fintype GroupType] :
    ∑ element, (Representation.leftRegular ℂ GroupType).character element = (Nat.card GroupType : ℂ) := by
  classical
  simp only [finite_group_regular_character]
  simp

theorem nonintegral_prime_inverse (prime : ℕ) (prime_prime : prime.Prime) :
    ¬IsIntegral ℤ ((prime : ℂ)⁻¹) := by
  intro integral
  have rational_integral : IsIntegral ℤ ((prime : ℚ)⁻¹) :=
    IsIntegral.tower_bot_of_field (B := ℂ) (by simpa only [map_inv₀, map_natCast] using integral)
  obtain ⟨integer, equal⟩ := IsIntegrallyClosed.isIntegral_iff.mp rational_integral
  change (integer : ℚ) = (prime : ℚ)⁻¹ at equal
  have rational_equal : (integer : ℚ) * (prime : ℚ) = 1 := by
    rw [equal, inv_mul_cancel₀]
    exact_mod_cast prime_prime.ne_zero
  have integer_equal : integer * (prime : ℤ) = 1 := by exact_mod_cast rational_equal
  have divides : (prime : ℤ) ∣ 1 := ⟨integer, by simpa only [mul_comm] using integer_equal.symm⟩
  have nat_divides : prime ∣ 1 := by exact_mod_cast divides
  exact prime_prime.not_dvd_one nat_divides

end CFSG.SignalizerFunctor.Helpers

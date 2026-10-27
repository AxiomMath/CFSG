module

public import CFSG.LocalAnalysis.SignalizerFunctor.CharacterIntegrality
public import CFSG.LocalAnalysis.SignalizerFunctor.SimpleGroupAlgebraModules
public import CFSG.LocalAnalysis.SignalizerFunctor.RegularSimpleMultiplicity
public import CFSG.LocalAnalysis.SignalizerFunctor.PrincipalCharacterInfrastructure
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.TotallySplit

public section

universe groupUniverse indexUniverse

namespace CFSG.SignalizerFunctor.Helpers

noncomputable def principalCharacterIndices
    {GroupType : Type groupUniverse} [Group GroupType]
    {IndexType : Type indexUniverse} [Fintype IndexType]
    (summands : IndexType → Submodule (MonoidAlgebra ℂ GroupType) (MonoidAlgebra ℂ GroupType)) : Finset IndexType := by
  classical
  exact Finset.univ.filter (fun index => ∀ selected : GroupType,
    (Representation.ofModule' (k := ℂ) (G := GroupType) (summands index)) selected = 1)

theorem regular_identity_principal_contribution
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    {IndexType : Type indexUniverse} [Fintype IndexType]
    (summands : IndexType → Submodule (MonoidAlgebra ℂ GroupType) (MonoidAlgebra ℂ GroupType))
    (simple : ∀ index, IsSimpleModule (MonoidAlgebra ℂ GroupType) (summands index))
    (identity : ∀ element : GroupType, (Representation.leftRegular ℂ GroupType).character element =
      ∑ index, (Module.finrank ℂ (summands index) : ℂ) *
        (Representation.ofModule' (k := ℂ) (G := GroupType) (summands index)).character element)
    (element : GroupType) :
    ∑ index ∈ principalCharacterIndices summands,
      (Module.finrank ℂ (summands index) : ℂ) *
        (Representation.ofModule' (k := ℂ) (G := GroupType) (summands index)).character element = 1 := by
  classical
  let : Fintype GroupType := Fintype.ofFinite GroupType
  let : ∀ index, FiniteDimensional ℂ (summands index) :=
    fun index => finite_group_algebra_submodule_finiteDimensional (summands index)
  let : ∀ index, IsSimpleModule (MonoidAlgebra ℂ GroupType) (summands index) := simple
  let : ∀ index, Nontrivial (summands index) :=
    fun index => IsSimpleModule.nontrivial (MonoidAlgebra ℂ GroupType) (summands index)
  let representation := fun index => Representation.ofModule' (k := ℂ) (G := GroupType) (summands index)
  let : ∀ index, (representation index).IsIrreducible :=
    fun index => simple_group_algebra_module_irreducible (summands index)
  let principal : IndexType → Prop := fun index => ∀ selected, representation index selected = 1
  let principalIndices := Finset.univ.filter principal
  have principal_rank : ∀ index, principal index → Module.finrank ℂ (summands index) = 1 :=
    fun index trivial_action => trivial_irreducible_degree_one (representation index) trivial_action
  have principal_character : ∀ index, principal index → ∀ selected, (representation index).character selected = 1 := by
    intro index trivial_action selected
    change (LinearMap.trace ℂ (summands index)) (representation index selected) = 1
    rw [trivial_action selected, LinearMap.trace_one, principal_rank index trivial_action]
    norm_num
  have character_total : ∀ index, ∑ selected, (representation index).character selected =
      if principal index then (Nat.card GroupType : ℂ) else 0 := by
    intro index
    split_ifs with trivial_action
    · simp only [principal_character index trivial_action, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
    · exact nontrivial_irreducible_character_sum_zero (representation index) trivial_action
  have total := congrArg (fun character : GroupType → ℂ => ∑ selected, character selected) (funext identity)
  rw [finite_group_regular_character_sum, Finset.sum_comm] at total
  change (Nat.card GroupType : ℂ) = ∑ index, ∑ selected,
    (Module.finrank ℂ (summands index) : ℂ) * (representation index).character selected at total
  simp_rw [← Finset.mul_sum, character_total] at total
  have total_equal : (Nat.card GroupType : ℂ) = (principalIndices.card : ℂ) * (Nat.card GroupType : ℂ) := by
    calc
      _ = ∑ index, (Module.finrank ℂ (summands index) : ℂ) *
          (if principal index then (Nat.card GroupType : ℂ) else 0) := total
      _ = ∑ index ∈ principalIndices, (Nat.card GroupType : ℂ) := by
        unfold principalIndices
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro index _member
        split_ifs with trivial_action
        · rw [principal_rank index trivial_action]
          norm_num
        · simp only [mul_zero]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have group_card_ne : (Nat.card GroupType : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have count_equal : (principalIndices.card : ℂ) = 1 :=
    (mul_right_cancel₀ group_card_ne) (by simpa only [one_mul] using total_equal.symm)
  have indices_equal : principalCharacterIndices summands = principalIndices := by
    ext index
    simp only [principalCharacterIndices, principalIndices, principal, representation, Finset.mem_filter]
  rw [indices_equal]
  change (∑ index ∈ principalIndices,
    (Module.finrank ℂ (summands index) : ℂ) * (representation index).character element) = 1
  calc
    _ = ∑ _index ∈ principalIndices, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro index member
      have trivial_action := (Finset.mem_filter.mp member).2
      rw [principal_rank index trivial_action, principal_character index trivial_action element]
      norm_num
    _ = 1 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, count_equal]

theorem regular_identity_prime_degree_escape
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    {IndexType : Type indexUniverse} [Fintype IndexType]
    (summands : IndexType → Submodule (MonoidAlgebra ℂ GroupType) (MonoidAlgebra ℂ GroupType))
    (simple : ∀ index, IsSimpleModule (MonoidAlgebra ℂ GroupType) (summands index))
    (identity : ∀ element : GroupType, (Representation.leftRegular ℂ GroupType).character element =
      ∑ index, (Module.finrank ℂ (summands index) : ℂ) *
        (Representation.ofModule' (k := ℂ) (G := GroupType) (summands index)).character element)
    (prime : ℕ) (prime_prime : prime.Prime) (element : GroupType) (element_ne : element ≠ 1) :
    ∃ index, (¬∀ selected : GroupType,
        (Representation.ofModule' (k := ℂ) (G := GroupType) (summands index)) selected = 1) ∧
      ¬prime ∣ Module.finrank ℂ (summands index) ∧
        (Representation.ofModule' (k := ℂ) (G := GroupType) (summands index)).character element ≠ 0 := by
  classical
  let : ∀ index, FiniteDimensional ℂ (summands index) :=
    fun index => finite_group_algebra_submodule_finiteDimensional (summands index)
  let representation := fun index => Representation.ofModule' (k := ℂ) (G := GroupType) (summands index)
  let principal : IndexType → Prop := fun index => ∀ selected, representation index selected = 1
  let nonprincipalIndices := Finset.univ.filter (fun index => ¬principal index)
  let terms : IndexType → ℂ := fun index => (Module.finrank ℂ (summands index) : ℂ) *
    (representation index).character element
  by_contra no_escape
  have term_integral : ∀ index ∈ nonprincipalIndices, IsIntegral ℤ (terms index / (prime : ℂ)) := by
    intro index member
    have nonprincipal := (Finset.mem_filter.mp member).2
    by_cases zero : (representation index).character element = 0
    · simp only [terms, zero, mul_zero, zero_div]
      exact isIntegral_zero
    have divides : prime ∣ Module.finrank ℂ (summands index) := by
      by_contra not_divides
      exact no_escape ⟨index, nonprincipal, not_divides, zero⟩
    obtain ⟨multiplicity, degree_equal⟩ := divides
    have equal : terms index / (prime : ℂ) = (multiplicity : ℂ) * (representation index).character element := by
      dsimp only [terms]
      rw [degree_equal, Nat.cast_mul]
      have prime_ne : (prime : ℂ) ≠ 0 := by exact_mod_cast prime_prime.ne_zero
      field_simp
    rw [equal]
    exact (isIntegral_natCast multiplicity).mul (finite_group_character_integral (representation index) element)
  let remainder : ℂ := ∑ index ∈ nonprincipalIndices, terms index / (prime : ℂ)
  have remainder_integral : IsIntegral ℤ remainder := IsIntegral.sum _ term_integral
  have remainder_equal : (prime : ℂ) * remainder = ∑ index ∈ nonprincipalIndices, terms index := by
    dsimp only [remainder]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _member
    have prime_ne : (prime : ℂ) ≠ 0 := by exact_mod_cast prime_prime.ne_zero
    field_simp
  have total := Finset.sum_filter_add_sum_filter_not Finset.univ principal terms
  have principal_equal := regular_identity_principal_contribution summands simple identity element
  change (∑ index ∈ Finset.univ.filter principal, terms index) = 1 at principal_equal
  rw [principal_equal, ← remainder_equal] at total
  have regular_zero : ∑ index, terms index = 0 := by
    rw [← identity element, finite_group_regular_character]
    simp only [ite_eq_right element_ne]
  rw [regular_zero] at total
  have prime_ne : (prime : ℂ) ≠ 0 := by exact_mod_cast prime_prime.ne_zero
  have remainder_value : remainder = -(prime : ℂ)⁻¹ := by
    apply (mul_left_cancel₀ prime_ne)
    rw [mul_neg, mul_inv_cancel₀ prime_ne]
    linear_combination total
  rw [remainder_value] at remainder_integral
  exact nonintegral_prime_inverse prime prime_prime (by simpa only [neg_neg] using remainder_integral.neg)

end CFSG.SignalizerFunctor.Helpers

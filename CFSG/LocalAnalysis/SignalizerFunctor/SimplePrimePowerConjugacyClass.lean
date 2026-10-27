module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeClassDegreeScalarAlternative
public import CFSG.LocalAnalysis.SignalizerFunctor.RegularCharacterDecomposition
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeDegreeCharacterEscape

public section

universe groupUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem simple_group_representation_injective
    {GroupType : Type groupUniverse} [Group GroupType] [IsSimpleGroup GroupType]
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    (representation : Representation ℂ GroupType VectorType)
    (nontrivial_action : ¬∀ element, representation element = 1) : Function.Injective representation := by
  rcases CFSG.eq_bot_or_eq_top_of_normal representation.ker inferInstance with trivial_kernel | full_kernel
  · exact representation.ker_eq_bot_iff.mp trivial_kernel
  · apply False.elim
    apply nontrivial_action
    intro element
    apply MonoidHom.mem_ker.mp
    rw [full_kernel]
    exact Subgroup.mem_top element

theorem injective_representation_scalar_central
    {GroupType : Type groupUniverse} [Group GroupType]
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    (representation : Representation ℂ GroupType VectorType) (injective : Function.Injective representation)
    (element : GroupType) (scalar : ℂ)
    (scalar_equal : representation element = scalar • (1 : Module.End ℂ VectorType)) :
    element ∈ Subgroup.center GroupType := by
  rw [Subgroup.mem_center_iff]
  intro selected
  apply injective
  rw [map_mul, map_mul, scalar_equal, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem nonprincipal_coprime_degree_character_exists
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (element : GroupType) (element_ne : element ≠ 1) :
    ∃ summand : Submodule (MonoidAlgebra ℂ GroupType) (MonoidAlgebra ℂ GroupType),
      IsSimpleModule (MonoidAlgebra ℂ GroupType) summand ∧
      (¬∀ selected : GroupType, (Representation.ofModule' (k := ℂ) (G := GroupType) summand) selected = 1) ∧
      ¬prime ∣ Module.finrank ℂ summand ∧
        (Representation.ofModule' (k := ℂ) (G := GroupType) summand).character element ≠ 0 := by
  classical
  obtain ⟨summands, finite, _internal, simple, identity⟩ := finite_group_regular_character_identity GroupType
  let : Fintype summands := finite.fintype
  let classes := Quotient (simpleSummandSetoid (fun summand : summands => summand.val))
  let : Fintype classes := Fintype.ofFinite classes
  dsimp only at identity
  obtain ⟨summandClass, nonprincipal, not_divides, nonzero⟩ := regular_identity_prime_degree_escape
    (fun summandClass : classes => summandClass.out.val)
    (fun summandClass => simple summandClass.out.val summandClass.out.property) identity prime prime_prime element element_ne
  exact ⟨summandClass.out.val, simple summandClass.out.val summandClass.out.property, nonprincipal, not_divides, nonzero⟩

theorem simple_group_prime_power_class_central
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType] [IsSimpleGroup GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (exponent : ℕ)
    (element : GroupType) (element_ne : element ≠ 1)
    (class_power : (conjugacyClassFinset element).card = prime ^ exponent) :
    element ∈ Subgroup.center GroupType := by
  classical
  obtain ⟨summand, simple, nonprincipal, not_divides, nonzero⟩ :=
    nonprincipal_coprime_degree_character_exists GroupType prime prime_prime element element_ne
  let : IsSimpleModule (MonoidAlgebra ℂ GroupType) summand := simple
  let : FiniteDimensional ℂ summand := finite_group_algebra_submodule_finiteDimensional summand
  let : Nontrivial summand := IsSimpleModule.nontrivial (MonoidAlgebra ℂ GroupType) summand
  let representation := Representation.ofModule' (k := ℂ) (G := GroupType) summand
  let : representation.IsIrreducible := simple_group_algebra_module_irreducible summand
  have degree_coprime : Nat.Coprime (Module.finrank ℂ summand) (conjugacyClassFinset element).card := by
    rw [class_power]
    have prime_coprime := (prime_prime.coprime_iff_not_dvd).mpr not_divides
    exact prime_coprime.symm.pow_right exponent
  rcases coprime_class_degree_scalar_alternative representation element degree_coprime with zero | scalar
  · exact False.elim (nonzero zero)
  · exact injective_representation_scalar_central representation
      (simple_group_representation_injective representation nonprincipal) element _ scalar

end CFSG.SignalizerFunctor.Helpers

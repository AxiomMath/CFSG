module

public import CFSG.LocalAnalysis.SignalizerFunctor.ClassSumIntegrality
public import CFSG.LocalAnalysis.SignalizerFunctor.AlgebraicIntegerCancellation
public import CFSG.LocalAnalysis.SignalizerFunctor.FiniteOrderScalarAlternative

public section

universe groupUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

@[expose] noncomputable def conjugacyClassFinset
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (element : GroupType) : Finset GroupType := by
  classical
  exact (Set.toFinite (ConjClasses.mk element).carrier).toFinset

theorem mem_conjugacyClassFinset
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (element selected : GroupType) : selected ∈ conjugacyClassFinset element ↔ IsConj element selected := by
  classical
  simp only [conjugacyClassFinset, Set.Finite.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]

theorem conjugacyClassFinset_invariant
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (element conjugator selected : GroupType) (member : selected ∈ conjugacyClassFinset element) :
    conjugator * selected * conjugator⁻¹ ∈ conjugacyClassFinset element := by
  rw [mem_conjugacyClassFinset] at member ⊢
  exact member.trans (isConj_iff.mpr ⟨conjugator, rfl⟩)

theorem conjugacyClassFinset_same_character
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    (representation : Representation ℂ GroupType VectorType) (element selected : GroupType)
    (member : selected ∈ conjugacyClassFinset element) :
    representation.character selected = representation.character element := by
  obtain ⟨conjugator, equal⟩ := isConj_iff.mp ((mem_conjugacyClassFinset element selected).mp member)
  rw [← equal]
  exact representation.char_conj element conjugator

theorem coprime_class_degree_character_ratio_integral
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    [FiniteDimensional ℂ VectorType] [Nontrivial VectorType]
    (representation : Representation ℂ GroupType VectorType) [representation.IsIrreducible]
    (element : GroupType)
    (coprime : Nat.Coprime (Module.finrank ℂ VectorType) (conjugacyClassFinset element).card) :
    IsIntegral ℤ (representation.character element / (Module.finrank ℂ VectorType : ℂ)) := by
  apply integral_coprime_quotient (representation.character element) (Module.finrank ℂ VectorType)
    (conjugacyClassFinset element).card (Module.finrank_pos (R := ℂ) (M := VectorType)) coprime
    (finite_group_character_integral representation element)
  exact irreducible_class_sum_central_character_integral representation (conjugacyClassFinset element)
    (conjugacyClassFinset_invariant element) element (conjugacyClassFinset_same_character representation element)

theorem coprime_class_degree_scalar_alternative
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    [FiniteDimensional ℂ VectorType] [Nontrivial VectorType]
    (representation : Representation ℂ GroupType VectorType) [representation.IsIrreducible]
    (element : GroupType)
    (coprime : Nat.Coprime (Module.finrank ℂ VectorType) (conjugacyClassFinset element).card) :
    representation.character element = 0 ∨
      representation element = (representation.character element / (Module.finrank ℂ VectorType : ℂ)) •
        (1 : Module.End ℂ VectorType) := by
  have finite_order : representation element ^ orderOf element = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  exact finite_order_integral_trace_ratio_scalar_alternative (representation element) (orderOf element)
    (orderOf_pos element) finite_order (coprime_class_degree_character_ratio_integral representation element coprime)

end CFSG.SignalizerFunctor.Helpers

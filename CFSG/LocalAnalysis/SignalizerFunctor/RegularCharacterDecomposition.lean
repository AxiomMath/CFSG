module

public import CFSG.LocalAnalysis.SignalizerFunctor.SemisimpleCharacterDecomposition
public import CFSG.LocalAnalysis.SignalizerFunctor.RegularSimpleMultiplicity

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem finite_group_regular_simple_decomposition
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType] :
    ∃ summands : Set (Submodule (MonoidAlgebra ℂ GroupType) (MonoidAlgebra ℂ GroupType)),
      ∃ finite : summands.Finite,
        DirectSum.IsInternal (fun summand : summands => summand.val) ∧
        (∀ summand ∈ summands, IsSimpleModule (MonoidAlgebra ℂ GroupType) summand) ∧
        (∀ element : GroupType, (Representation.leftRegular ℂ GroupType).character element =
          ∑ summand ∈ finite.toFinset,
            (Representation.ofModule' (k := ℂ) (G := GroupType) summand).character element) := by
  classical
  let : Fintype GroupType := Fintype.ofFinite GroupType
  let : FiniteDimensional ℂ (MonoidAlgebra ℂ GroupType) :=
    Module.Finite.of_basis (MonoidAlgebra.basis GroupType ℂ)
  obtain ⟨summands, finite, independent, spanning, simple, character⟩ :=
    group_algebra_simple_character_decomposition (GroupType := GroupType) (MonoidAlgebra ℂ GroupType)
  refine ⟨summands, finite, ?_, simple, ?_⟩
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      ((sSupIndep_iff summands).mp independent)
    rw [iSup_subtype]
    rwa [sSup_eq_iSup] at spanning
  · rwa [group_algebra_regular_representation] at character

theorem finite_group_regular_character_identity
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType] :
    ∃ summands : Set (Submodule (MonoidAlgebra ℂ GroupType) (MonoidAlgebra ℂ GroupType)),
      ∃ finite : summands.Finite,
        DirectSum.IsInternal (fun summand : summands => summand.val) ∧
        (∀ summand ∈ summands, IsSimpleModule (MonoidAlgebra ℂ GroupType) summand) ∧
        (let _ : Finite summands := finite.to_subtype
         let classes := Quotient (simpleSummandSetoid (fun summand : summands => summand.val))
         let _ : Fintype classes := Fintype.ofFinite classes
         ∀ element : GroupType, (Representation.leftRegular ℂ GroupType).character element =
           ∑ summandClass : classes,
             (Module.finrank ℂ summandClass.out.val : ℂ) *
               (Representation.ofModule' (k := ℂ) (G := GroupType) summandClass.out.val).character element) := by
  classical
  obtain ⟨summands, finite, internal, simple, character⟩ := finite_group_regular_simple_decomposition GroupType
  refine ⟨summands, finite, internal, simple, ?_⟩
  let : Fintype summands := finite.fintype
  let : Fintype (Quotient (simpleSummandSetoid (fun summand : summands => summand.val))) := Fintype.ofFinite _
  dsimp only
  intro element
  apply regular_simple_character_identity (fun summand : summands => summand.val) internal
    (fun summand => simple summand.val summand.property)
  intro selected
  rw [character selected]
  exact Finset.sum_subtype finite.toFinset (fun _summand => Set.Finite.mem_toFinset finite) _

end CFSG.SignalizerFunctor.Helpers

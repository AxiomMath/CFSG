module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem rIso153_holds : RIso153 := by
  intro X _
  constructor
  · intro h
    exact CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel h
  · rintro ⟨e⟩
    obtain ⟨e'⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_statedProj_of_alternating_eight e
    refine Or.inl ⟨by decide, ?_⟩
    unfold StatedClassicalModel
    refine ⟨?_, ?_⟩
    · unfold StatedLieAdmissible
      refine ⟨Nat.prime_two, le_rfl, ?_⟩
      simp
    · exact ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨e'⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

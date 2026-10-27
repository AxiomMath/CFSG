module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CorePart23
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreQ8D8
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreA5Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem core49_of_inputs (hI : Inputs49) :
    ∀ (G : Type) [Group G] [Finite G] (H X L Q I : Subgroup G),
      Setup49 H X L Q I → KI49 X I → Concl49 H X L Q I := by
  intro G _ _ H X L Q I h hK
  exact concl49_iff.mpr ⟨part1_49 hI h hK, part2_49 hI h hK, part3_49 hI h hK⟩

theorem inputs49 : Inputs49 := ⟨fiveRankBound, q8d8Counts, a5MinusModule⟩

theorem core49 :
    ∀ (G : Type) [Group G] [Finite G] (H X L Q I : Subgroup G),
      Setup49 H X L Q I → KI49 X I → Concl49 H X L Q I :=
  core49_of_inputs inputs49

theorem k49I_core49 : K49I := k49I_of_core core49

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

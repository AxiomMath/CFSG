module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainExclA
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainExclB
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainSetupG

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

theorem nm_FK_le (hG : GoldExclusionSylow) {X : Type} [Group X] [Finite X]
    (S : N7MSetup X) : ∀ A ∈ nmFK, ∃ x, S.ρ x = A := by
  rcases nm_normalizer_cases S with hY | hFK
  · exfalso
    refine nm_not_weak hG S ?_
    intro x g hx hg
    by_contra hxE6
    exact nm_exclB S hY hx (by simpa only [map_mul, map_inv] using hg)
      (by simpa only [map_mul, map_inv] using hxE6)
  · exact hFK

theorem l1N7Main_of_goldSylow (hG : GoldExclusionSylow) : L1N7Main :=
  l1N7Main_of_setupFK fun _ _ _ S => nm_FK_le hG S

end CFSG.StandardType.FrameRoute.FS81

end

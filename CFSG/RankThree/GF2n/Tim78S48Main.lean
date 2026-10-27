module

public import CFSG.RankThree.GF2n.Tim78S4Final
public import CFSG.RankThree.GF2n.Tim78S48End
import CFSG.RankThree.GF2n.Tim78S48Phase
import CFSG.RankThree.GF2n.Tim78S48Aff
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

namespace Tim78

namespace Hyp4

variable {G : Type} [Group G] [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Step48

theorem tim78_4_8 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    Step48 M B P T := by
  intro g h48
  by_contra hP
  have hphase1 : ∀ g' : G, Hyp48 M B T g' → ¬ conjSubgroup g' B ≤ P → Phase1 B T g' :=
    fun g' h hP' => H.phase1 hCen hU h hP'
  obtain ⟨C, L, E⟩ := H.exists_endgameData hCen hU hphase1 h48 hP (hphase1 g h48 hP)
  exact H.endgame hCen hU hphase1 E

end Step48

end Hyp4

end Tim78

open Tim78

section Final

theorem tim78Sec4_of_rootType
    (hRT : ∀ (G : Type) [Group G] [Finite G] (M B Q P T : Subgroup G), Hyp4 M B Q P T →
      RootTypeStep M B) : Tim78Sec4Statement :=
  tim78Sec4_of_rootType_step48 hRT
    (fun _ _ _ _ _ _ _ _ H =>
      H.tim78_4_8 CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput)

end Final

end CFSG.RankThree.GF2n

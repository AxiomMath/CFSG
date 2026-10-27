module

public import CFSG.Timmesfeld.Bridge.RootSetsConn15
public import CFSG.Timmesfeld.Bridge.RootSetsConn18
public import CFSG.Timmesfeld.Bridge.RootSetsConn19
public import CFSG.Timmesfeld.Bridge.OddTranspMain

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem threeClasses (hC : ConnCex D) (h : Step6 D a b c x z P) : ThreeClasses D x P := by
  rcases h.psl2_or_sz OddTransp.oddTranspBender hC with hL2 | ⟨m, hm, ⟨e⟩⟩
  · exact h.threeClasses_of_psl2 OddTransp.oddTranspBender hC hL2
  · exact (h.false_of_sz OddTransp.oddTranspBender hC hm e).elim

end Step6

theorem step6ThreeClassesHyp : Step6ThreeClassesHyp := fun _ _ _ _ _ _ _ _ _ hC h =>
  h.threeClasses hC

theorem tim75Thm31 : Moufang.Tim75Thm31 :=
  tim75Thm31_of' OddTransp.oddTranspBender step6ThreeClassesHyp

end CFSG.Timmesfeld.Bridge

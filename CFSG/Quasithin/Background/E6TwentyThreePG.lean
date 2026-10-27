module

public import CFSG.Quasithin.Background.E6TwentyThreePB
public import CFSG.Quasithin.Background.E6TwentyThreePC
public import CFSG.Quasithin.Background.E6TwentyThreePD
public import CFSG.Quasithin.Background.E6TwentyThreePF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdFam
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporMain
public import CFSG.Quasithin.Background.E6TwentyThreeO

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

theorem e623A6Insp_holds :
    E623A6Insp := by
  intro G _ _ Y E X a z hq hlist helem hnorm ha hnc hcomp ha6 hstar hdisj
  have h : InspHyp Y E X a z := ⟨hq, hlist, helem, hnorm, ha, hnc, hcomp, ha6, hstar⟩
  obtain ⟨-, -, hpat⟩ := h.patterns (Id2519.tabIdent_of_families Id2519.identFamilies_proved)
  rcases hdisj with ⟨S, hS, hES⟩ | h8
  · exact h.false_of_sylow Spor.e68CentComp_holds hS hES
  · rcases hpat with hSp | hL5 | hHS | hA8
    · exact h.false_of_patSp4 hSp h8
    · exact h.false_of_patL5 hL5 h8
    · exact h.false_of_patHS hHS h8
    · exact h.false_of_patA8 hA8 h8

end CFSG.Quasithin.E6

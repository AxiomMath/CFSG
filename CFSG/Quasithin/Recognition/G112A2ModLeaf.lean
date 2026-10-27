module

public import CFSG.Quasithin.Recognition.G112A2D6Heis
public import CFSG.Quasithin.Recognition.G112A2D6Orth
public import CFSG.Quasithin.Recognition.G112A2D6Alt
public import CFSG.Quasithin.Recognition.G112A2D8Orth
public import CFSG.Quasithin.Recognition.G112A2ModTen
public import CFSG.GH74.QTGen4.Leaves.G112Core

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChG

theorem g112ConclA2Mod_of_open (o6 : G112A2OpenConcl6) (o6' : G112A2OpenConcl6U33)
    (o7 : G112A2OpenConcl7) (o9 : G112A2OpenConcl9) (o11 : G112A2OpenConcl11) :
    G112ConclA2Mod := by
  intro V _ _ _ B Γ v₁ W X X₀ hH hcon hd
  rcases hcon with hcon | hcon
  · rcases hcon with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11 | c12 | c13
    · exfalso
      have := c1.1
      omega
    · exact CFSG.GH74.QTGen4.Leaves.G112.g112ConclA2_d4_holds V B Γ v₁ W X X₀ hH c2
    · exact g112ConclA2_concl3 B Γ v₁ W X X₀ hH (G112Concl3.toPartial c3)
    · exact g112ConclA2_concl4 B Γ v₁ W X X₀ hH c4
    · exact g112ConclA2_concl5 B Γ v₁ W X X₀ hH c5
    · exact o6 V B Γ v₁ W X X₀ hH c6
    · exact o7 V B Γ v₁ W X X₀ hH c7
    · exact g112ConclA2_concl8 B Γ v₁ W X X₀ hH c8
    · exact o9 V B Γ v₁ W X X₀ hH c9
    · exact g112ConclA2_concl10Mod hH c10
    · exact o11 V B Γ v₁ W X X₀ hH c11
    · exact g112ConclA2_concl12 B Γ v₁ W X X₀ hH c12
    · exact g112ConclA2_concl13Mod B Γ v₁ W X X₀ hH c13
  · exact o6' V B Γ v₁ W X X₀ hH hcon

end CFSG.Quasithin.G112A2

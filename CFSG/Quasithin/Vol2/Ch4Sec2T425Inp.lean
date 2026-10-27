module

public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.Quasithin.Vol2.Ch1A3Proved
public import CFSG.Quasithin.Background.GoldschmidtTDC19
public import CFSG.Quasithin.Background.GoldschmidtTDC111Main
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.A38Facts
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Vol2.Ch4Sec2T425H

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Quasithin


theorem inp425_holds
    (G : Type) [Group G] [Finite G] : Inp425 G :=
  ⟨CFSG.Quasithin.H13.VolI.a36ForSQTK_holds, CFSG.Quasithin.a37ForSQTK_proved,
    CFSG.Quasithin.a38ForSQTK_proved, CFSG.Quasithin.a39ForSQTK_proved,
    CFSG.Quasithin.H13.VolI.asc129Statement_holds G, CFSG.Quasithin.asc111Statement_holds G,
    CFSG.Quasithin.asc19Statement_holds G,
    CFSG.Quasithin.a3Orbits_of_facts CFSG.SectionRank.QTK.CentreFact.a36Facts_holds
      CFSG.SectionRank.QTK.CentreFact.a38Facts_holds⟩

theorem thm4_2_5_of_c27
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) :
    Thm4_2_5 :=
  thm4_2_5_of (fun G _ _ => inp425_holds G) hC27

end CFSG.Quasithin.H13.Ch4

module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzLtMain
public import CFSG.Quasithin.Background.F918D36Holds
public import CFSG.Quasithin.Background.F918J6
public import CFSG.Quasithin.Background.SmithD321Holds
public import CFSG.Quasithin.Vol2.Ch1A3Proved

public section

namespace CFSG.Quasithin.H13.P31Sz

section Cert

theorem noSzLtF_w31_final
    (h1222 : Stmt12_2_2) : NoSzLtF_w31 := by
  have hA37 : CFSG.Quasithin.A37ForSQTK := CFSG.Quasithin.a37ForSQTK_proved
  have hA38 : CFSG.Quasithin.A38ForSQTK := CFSG.Quasithin.a38ForSQTK_proved
  have hA21 : CFSG.Quasithin.AsA21SQTKSection := CFSG.Quasithin.asA21SQTKSection
  have h45 : CFSG.Quasithin.AsB45 := CFSG.Quasithin.asB45_holds
  have hF : CFSG.Quasithin.Vol2.Ch10.SecA.Facts10_1 :=
    CFSG.Quasithin.Vol2.Ch10.SecA.facts10_1_holds
  have hNS : CFSG.Quasithin.Insp5aNonShape := CFSG.Quasithin.insp5aNonShape_holds
  have h321 : CFSG.Quasithin.D321 := by
    intro W _ _ M Mp T L V hD t htT htn hMp hq _ _ _ _ _ _ _ _
    exact CFSG.Quasithin.d321_holds W M Mp T L V hD t htT htn hMp hq
  exact noSzLtF_w31_of CFSG.Quasithin.H13.KGSz.szEnd_holds CFSG.Quasithin.d36_holds
    CFSG.Quasithin.d37_holds h321 (CFSG.Quasithin.insp5a_of_inputs hA21 h45 hF hNS) hA37 hA38 h1222

end Cert

end CFSG.Quasithin.H13.P31Sz

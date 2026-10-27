module

public import CFSG.Quasithin.Background.E2TwoProofMain
public import CFSG.Quasithin.Background.C129NativeLight
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Background.E2TwoProofAlt
public import CFSG.Quasithin.Background.E2TwoProofExc
public import CFSG.Quasithin.Background.E2TwoProofOddL2
public import CFSG.Quasithin.Background.E2TwoProofSporLat
public import CFSG.Quasithin.Background.E2TwoProofSporM12
public import CFSG.Quasithin.Background.E2TwoProofSporM23
public import CFSG.Quasithin.Background.E2TwoProofSporJ1
public import CFSG.Quasithin.Background.E2TwoProofSporJ2

public section

namespace CFSG.Quasithin

namespace E2P

theorem e22SporTenFam :
    E22SporTenFam := by
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SporB.asc86bClauseB_M11
  · exact SporB.asc86bClauseB_M12
  · exact SporB.asc86bClauseB_M22
  · exact SporB.asc86bClauseB_M23
  · exact SporB.asc86bClauseB_M24
  · exact SporB.asc86bClauseB_J1
  · exact SporB.asc86bClauseB_J2
  · exact SporB.asc86bClauseB_HS
  · exact SporB.asc86bClauseB_He
  · exact SporB.asc86bClauseB_Ru

theorem e22Families_of_cited
    (h80 : Asc80L3Eps) (h86 : Asc86bSporadic) : E22Families :=
  ⟨e22AltFam, e22BenderFam, e22L3Sp4Fam, e22Char2ExcFam, e22LnTwoFam, e22OddL2Fam, h80,
    e22SporTenFam, h86⟩

theorem e22StatementNoN_of_cited
    (h80 : Asc80L3Eps) (h86 : Asc86bSporadic) : E2.E22StatementNoN :=
  e22StatementNoN_of_inputs
    ⟨e22AltFam, e22BenderFam, e22L3Sp4Fam, e22Char2ExcFam, e22LnTwoFam, e22OddL2Fam, h80,
      e22SporTenFam, h86⟩
    CFSG.QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved C129Native.a38ForSQTKCat_proved
    a23SQTKListFact asA21SQTKSection

end E2P

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.E6EighteenH
public import CFSG.Quasithin.Background.E6EighteenI
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

theorem noA7Fix_sporadic
    (s : TauCeti.SporadicName) (hs : IsLemma115SporadicName s) (hHe : s ≠ .He) :
    IsSimpleGroup (NativeSporadic.Carrier s) ∧ NoA7Fix (NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2, noA7Fix_m11⟩
  · exact ⟨CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2, noA7Fix_m12⟩
  · exact ⟨CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2, noA7Fix_m22⟩
  · exact ⟨CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2, noA7Fix_m23⟩
  · exact ⟨CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2, noA7Fix_m24⟩
  · exact ⟨CFSG.Sporadic.J2.isSimpleGroup_J2, noA7Fix_j2⟩
  · exact ⟨CFSG.Sporadic.J4.isSimpleGroup_J4, noA7Fix_j4⟩
  · exact ⟨CFSG.Sporadic.HS.isSimpleGroup_HS, noA7Fix_hs⟩
  · exact absurd rfl hHe
  · exact ⟨CFSG.Sporadic.Ru.isSimpleGroup_Ru, noA7Fix_ru⟩

theorem noA7FixL115NotHe_holds :
    NoA7FixL115NotHe := by
  refine noA7FixL115NotHe_of ?_ (fun X _ _ h => noA7Fix_psu33 h) (fun X _ _ h => noA7Fix_psl33 h)
    (fun X _ _ p _ h => noA7Fix_psl2_odd h) noA7Fix_sporadic
  intro X _ _ hs hab h
  obtain ⟨a, b, hab⟩ := hab
  exact noA7Fix_sqtkCharTwoLie hab h

end E6

end CFSG.Quasithin

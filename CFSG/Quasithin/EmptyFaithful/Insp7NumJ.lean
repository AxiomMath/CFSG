module

public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.J2
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

namespace Insp7

theorem isSimpleGroup_carrier_small
    {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) :
    IsSimpleGroup (NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  · exact CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  · exact CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  · exact CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  · exact CFSG.Sporadic.J2.fam_j2_simplicity.2.2

end Insp7

end CFSG.Quasithin

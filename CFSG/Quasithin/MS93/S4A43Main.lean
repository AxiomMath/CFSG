module

public import CFSG.Quasithin.MS93.S4A432O
public import CFSG.Quasithin.MS93.S4A43XK
public import CFSG.Quasithin.MS93.S4A431G

public section

namespace CFSG.Quasithin.MS93

theorem s43_of_cff (hF : S4A.S4CFF) (h32 : S32) : S43 := by
  have h4 := S4A.s43b4_of_cff hF h32
  have hA := S4A.s431A_of hF h32 h4
  have hB := S4A.s431B_of h32 hA
  exact s43_of_parts h4 (S4A.s43b6_of h32 hA hB (S4A.s432_holds h32 hA hB))

end CFSG.Quasithin.MS93

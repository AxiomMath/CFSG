module

public import CFSG.Quasithin.Vol2.KGFactC31J1
public import CFSG.Quasithin.Vol2.KGFactC31M11
public import CFSG.Quasithin.Vol2.KGFactC31M12
public import CFSG.Quasithin.Vol2.KGFactC31J2
public import CFSG.Quasithin.Vol2.KGFactC31M22
public import CFSG.Quasithin.Vol2.KGFactC31M23
public import CFSG.Quasithin.Vol2.KGFactC31M24
public import CFSG.Quasithin.Vol2.KGFactC31HS
public import CFSG.Quasithin.Vol2.KGFactC31He

public section

namespace CFSG.Quasithin.KGC31

theorem inspC31Sporadic_of
    (hRu : CFSG.Quasithin.InspC31SporadicAt .Ru) (hJ4 : CFSG.Quasithin.InspC31SporadicAtJ .J4) :
    CFSG.Quasithin.InspC31Sporadic := by
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inspC31SporadicAt_m11.toJ
  · exact inspC31SporadicAt_m12.toJ
  · exact M22.inspC31SporadicAt_m22.toJ
  · exact M23.inspC31SporadicAt_m23.toJ
  · exact M24.inspC31SporadicAt_m24.toJ
  · exact inspC31SporadicAt_j1.toJ
  · exact inspC31SporadicAt_j2.toJ
  · exact hJ4
  · exact HS.inspC31SporadicAt_hs.toJ
  · exact He.inspC31SporadicAt_he.toJ
  · exact hRu.toJ

end CFSG.Quasithin.KGC31

end

module

public import CFSG.Quasithin.H13.LocDblHSCheck
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Sporadic.HS.Native (hsData)

theorem sylowNoDouble_HS_group :
    SylowNoDouble ↥(J hsData) :=
  HSCert.hs_sylowNoDouble

theorem sylowNoDouble_HS :
    SylowNoDouble (Carrier .HS) := by
  have hF : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts
  have h : SylowNoDouble CFSG.Blueprint.NativeSporadic.HS :=
    SylowNoDouble.of_mulEquiv (A := ↥(J hsData)) (A' := CFSG.Blueprint.NativeSporadic.HS)
      (seedEquiv hF.toBaseFacts).symm sylowNoDouble_HS_group
  exact h

end CFSG.Quasithin.H13.LocDbl

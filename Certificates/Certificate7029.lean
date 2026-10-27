module

public import CFSG.Quasithin.H13.LocDblOdd
import CFSG.Quasithin.H13.LocDblHSLat

public section

namespace Certificates

open CFSG.Quasithin.H13.LocDbl CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.HS.Native (hsData) in
theorem certificate7029 : SylowNoDouble ↥(J hsData) ∧ OddIndexBound ↥(J hsData) [7680, 10752] :=
  ⟨CFSG.Quasithin.H13.LocDbl.sylowNoDouble_HS_lat, CFSG.Quasithin.H13.LocDbl.oddIndexBound_HS_lat⟩

end Certificates

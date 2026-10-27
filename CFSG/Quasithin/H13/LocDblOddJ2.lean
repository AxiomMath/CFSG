module

public import Certificates.Certificate7031

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.J2
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem oddIndexBound_J2_group :
    OddIndexBound ↥J [1152, 1920] :=
  Certificates.certificate7031.2

theorem oddIndexBound_J2 :
    OddIndexBound CFSG.Blueprint.NativeSporadic.J2 [1152, 1920] := by
  have h := oddIndexBound_J2_group
  exact OddIndexBound.of_mulEquiv (A := ↥J) (A' := CFSG.Blueprint.NativeSporadic.J2)
    nativeEquiv.symm h

end CFSG.Quasithin.H13.LocDbl

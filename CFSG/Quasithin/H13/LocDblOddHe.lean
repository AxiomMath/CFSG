module

public import Certificates.Certificate7030

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.He
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem oddIndexBound_He_group :
    OddIndexBound ↥J [138240, 138240, 21504] :=
  Certificates.certificate7030.2.1

theorem oddIndexBound_He :
    OddIndexBound CFSG.Blueprint.NativeSporadic.He [138240, 138240, 21504] := by
  have h := oddIndexBound_He_group
  exact OddIndexBound.of_mulEquiv (A := ↥J) (A' := CFSG.Blueprint.NativeSporadic.He)
    heEquivJ.symm h

end CFSG.Quasithin.H13.LocDbl

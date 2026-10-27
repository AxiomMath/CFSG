module

public import Certificates.Certificate7031

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Sporadic.J2
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem sylowNoDouble_J2_group :
    SylowNoDouble ↥J :=
  Certificates.certificate7031.1

theorem sylowNoDouble_J2 :
    SylowNoDouble (Carrier .J2) := by
  have h : SylowNoDouble CFSG.Blueprint.NativeSporadic.J2 :=
    SylowNoDouble.of_mulEquiv (A := ↥J) (A' := CFSG.Blueprint.NativeSporadic.J2) nativeEquiv.symm
      sylowNoDouble_J2_group
  exact h

end CFSG.Quasithin.H13.LocDbl

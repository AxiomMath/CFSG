module

public import Certificates.Certificate318002
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Blueprint
open CFSG.Quasithin.H13.LocDbl.M24Prof

theorem m24_profile :
    ∀ E : Subgroup ↥NativeSporadic.M24, IsElemAbelian 2 E → 32 ≤ Nat.card E → ProfileOK E :=
  Certificates.certificate318002

end CFSG.Quasithin.H13.LocDbl

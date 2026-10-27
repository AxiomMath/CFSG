module

public import Certificates.Data.DcHSOut
import Certificates.Kernel.HS589207.Final

public section

open CFSG.Quasithin.H13.LocDbl.HSLoc

public section

namespace Certificates

open CFSG.Quasithin.H13.LocDbl.HSLoc in
theorem certificate589207 : e0OK = true ∧ goodOK = true ∧ mooreOK = true ∧ cjOK = true :=
  ⟨CFSG.KD.HS589207.Final.e0_ok, CFSG.KD.HS589207.Final.good_ok,
    CFSG.KD.HS589207.Final.moore_ok, CFSG.KD.HS589207.Final.cj_ok⟩

end Certificates

end

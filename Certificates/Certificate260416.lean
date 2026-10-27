module

public import Certificates.Data.SmithB45HM22Nor
import CFSG.Certificates.Kernel.B45HM22Sound
import Certificates.Kernel.C260416.Pow
import Certificates.Kernel.C260416.N6
import Certificates.Kernel.C260416.N45
import Certificates.Kernel.C260416.N45c
import Certificates.Kernel.C260416.N84

public section

open CFSG.Quasithin.HM22 CFSG.KC.B45HM22 CFSG.KD.C260416

namespace Certificates

open CFSG.Quasithin.HM22 in
theorem certificate260416 : norCheck6 = true ∧ norCheck15 = true ∧ norCheck45 = true ∧ norCheck45c = true ∧
    norCheck84 = true := by
  obtain ⟨p6, p15, p45, p45c, p84⟩ := pow_all
  exact ⟨nortonOK_of_norP p6 chk6, nortonOK_of_norP p15 chk15, nortonOK_of_norP p45 chk45,
    nortonOK_of_norP p45c chk45c, nortonOK_of_norP p84 chk84⟩

end Certificates

end

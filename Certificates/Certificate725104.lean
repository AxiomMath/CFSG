module

public import Certificates.Data.AltInsp443
import Certificates.Kernel.Insp443Alt.Checks9
import CFSG.Certificates.Kernel.Insp443Alt.InvolSound

public section

open CFSG.SectionRank.QTK.Insp443.Alt

public section

namespace Certificates

open CFSG.SectionRank.QTK.Insp443.Alt CFSG.Certificates.Kernel.Insp443Alt

open CFSG.SectionRank.QTK.Insp443.Alt in
theorem certificate725104 : chk 9 () = true := by
  unfold chk
  exact decide_eq_true (altProp_of_chkI chkI9 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

end Certificates

end

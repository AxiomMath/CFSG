module

public import Certificates.Data.HuppertD4Q2.Checker
import CFSG.Certificates.Kernel.HD4Q2KSound
import Certificates.Kernel.HuppertD4Q2.Checks

public section

namespace Certificates

open CFSG.KD.D4Plane (ls lettersOK)

theorem certificate188008 : HuppertD4Q2.classChecks () = true :=
  CFSG.KC.HD4Q2K.classChecks_of (ls := ls)
    (fun i hi => beq_iff_eq.1 (List.all_eq_true.1 lettersOK i (List.mem_range.2 hi)))
    CFSG.KD.HD4Q2.classOK

end Certificates

module

public import Certificates.Data.HuppertD4Q2.Checker
import CFSG.Certificates.Kernel.HD4Q2KSound
import Certificates.Kernel.HuppertD4Q2.Checks

public section

namespace Certificates

open CFSG.KD.D4Plane (ls lettersOK)

theorem certificate188007 : HuppertD4Q2.planeCoverCheck () = true :=
  CFSG.KC.HD4Q2K.planeCoverCheck_of (ls := ls) (es := CFSG.KD.HD4Q2.es) (prs := CFSG.KD.HD4Q2.prs)
    (R1 := CFSG.KD.HD4Q2.r1) (R2 := CFSG.KD.HD4Q2.r2) (recs := CFSG.KD.HD4Q2.recs)
    (fun i hi => beq_iff_eq.1 (List.all_eq_true.1 lettersOK i (List.mem_range.2 hi)))
    CFSG.KD.HD4Q2.enumOK CFSG.KD.HD4Q2.sylowOK CFSG.KD.HD4Q2.prsOK CFSG.KD.HD4Q2.rowsOK
    CFSG.KD.HD4Q2.recsOK CFSG.KD.HD4Q2.coverOK

end Certificates

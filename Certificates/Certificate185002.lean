module

public import Certificates.Data.Sylow185.D42Center
import CFSG.Certificates.Kernel.HD4Q2KSound
import Certificates.Kernel.HuppertD4Q2.Checks

public section

namespace Certificates

open CFSG.KD.D4Plane (ls lettersOK)

theorem certificate185002 : HuppertD4Q2.centerCheck () = true :=
  CFSG.KC.HD4Q2K.centerCheck_of (ls := ls) (es := CFSG.KD.HD4Q2.es)
    (fun i hi => beq_iff_eq.1 (List.all_eq_true.1 lettersOK i (List.mem_range.2 hi)))
    CFSG.KD.HD4Q2.enumOK CFSG.KD.HD4Q2.sylowOK CFSG.KD.HD4Q2.centerOK

end Certificates

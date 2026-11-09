module

public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.T_Sel
public import CFSG.Certificates.Kernel.He.Bound.LabRange
import Certificates.Kernel.J3.Labs
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelCosetJ.Suz2.TL

open CFSG.KC.HeB

theorem labsPV : labRangeK CFSG.KD.CJSuz2T.PVs 0 32 = true := by quickRfl

theorem labWF_PV (x : Nat) : labWF (CFSG.KD.CJSuz2T.PVs (Nat.land x 31)) = true := by
  have h := labRangeK_sound labsPV (Nat.land x 31) (Nat.lt_succ_of_le Nat.and_le_right)
  rwa [Nat.zero_add] at h

end CertificateChecks.KernelCosetJ.Suz2.TL

public section

theorem CertificateChecks.KernelCosetJ.Suz2.TL.labsWF :
    CFSG.KC.HeB.labsWF CFSG.KD.CJSuz2T.LB (nat_lit 1169643) = true :=
  CFSG.KC.HeB.allBelow_of (m := 1169643) (f := fun i => CFSG.KC.HeB.labWF (CFSG.KD.CJSuz2T.LB i))
    (fun _ _ => CertificateChecks.KernelCosetJ.Suz2.TL.labWF_PV _)
    (Nat.succ (Nat.shiftRight 1169643 6))

end

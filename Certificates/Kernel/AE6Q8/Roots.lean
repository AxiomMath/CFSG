module

public import Certificates.Kernel.AE6Q8.Cls
public import Certificates.Kernel.AE6Q8.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Q8

open CFSG.KS CFSG.KC.Enum CFSG.KS.SporSch.MOC

theorem kZc : Nat.beq (SR.RP SR.zc) SK.zp = true := by decide +kernel

theorem kXHd : xHdK 360 9 (mask 9) (360 * 9) SR.GS SR.GSI SR.X SR.XI SR.XW SR.nx = true := by
  decide +kernel

theorem kClsX : allN SK.ncl (clsXK 360 9 (mask 9) (360 * 9) 5 SR.nx SC.LR SC.TR SK.E SR.RP SR.X
    SR.UO SR.CU SR.JO SR.CJ) = true := by
  decide +kernel

theorem kRootHd : rootHdK 360 9 (mask 9) (360 * 9) SC.BP 5 SC.LR SC.TR SK.E SK.O SR.RP SR.RO
    SR.KL SK.ncl SR.R = true := by
  decide +kernel

theorem kSq (b : Nat) (hb : b < 8) : allBlk (b * 512) (sqK 360 9 (mask 9) (360 * 9) SC.BP 5
    SC.LR SC.TR SR.RL SR.RC SR.RI SR.KL SK.ncl SR.R) 512 = true := by
  match b, hb with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => decide +kernel
  | 4, _ => decide +kernel
  | 5, _ => decide +kernel
  | 6, _ => decide +kernel
  | 7, _ => decide +kernel

theorem kRoot : allN SR.R (rootK SK.N SR.RL SR.RC SR.RI SR.RO SK.ncl) = true := by
  decide +kernel

theorem kCut : allN SR.R (cutK 360 9 (mask 9) (360 * 9) SC.BP 5 SC.LR SC.TR SC.TRI SR.RL SR.RC
    SR.UO SR.CU SR.X SR.XI SR.CT SR.CP) = true := by
  decide +kernel

end CertificateChecks.KernelAE6Q8

end

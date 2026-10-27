module

public import Certificates.Kernel.ChengHeld.PropsAut
public import Certificates.Data.Kernel.ChengHeldS4K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ChengHeldS2 CFSG.KC.ChengHeldP
open CFSG.OddStandard.ChengHeldData CertificateChecks.KernelChengHeld

theorem p6138_s4lt : ((List.range 7).all (fun j => Nat.blt (h0 j) 256) &&
    (List.range 7).all (fun j => Nat.blt (h1 j) 256)) = true := by
  decide +kernel

theorem p6138_s4cl0 : (clW 256 n0 [h0 0] 8 && clW 256 n0 [h0 0, h0 1, h0 2] 8 &&
    clW 256 n0 [h0 0, h0 1, h0 2, h0 3, h0 4] 8 && clW 256 n0 [h0 0, h0 1, h0 2, h0 5, h0 6] 8 &&
    clW 256 n0 [pwK n0 (h0 0) 2, h0 1, n0 (h0 0) (h0 2)] 8 && clW 256 n0 [1, 16, 32, 68, 92] 8 &&
    clW 256 n0 [h0 0, h0 1, n0 (h0 0) (h0 2)] 8 && clW 256 n0 [pwK n0 (h0 0) 2] 8) = true := by
  decide +kernel

theorem p6138_s4cl1 : (clW 256 n1 [h1 0] 8 && clW 256 n1 [h1 0, h1 1, h1 2] 8 &&
    clW 256 n1 [h1 0, h1 1, h1 2, h1 3, h1 4] 8 && clW 256 n1 [h1 0, h1 1, h1 2, h1 5, h1 6] 8 &&
    clW 256 n1 [pwK n1 (h1 0) 2, h1 1, n1 (h1 0) (h1 2)] 8 && clW 256 n1 [1, 16, 32, 68, 92] 8 &&
    clW 256 n1 [h1 0, h1 1, n1 (h1 0) (h1 2)] 8 && clW 256 n1 [pwK n1 (h1 0) 2] 8) = true := by
  decide +kernel

theorem p6138_s4d0 : derW 256 n0 j0 [h0 0, h0 1, h0 2, h0 3, h0 4, h0 5, h0 6] [h0 0, h0 1, h0 2]
    (fun a => decide (a < 256)) [(72, 84), (4, 192), (4, 96)] 8 = true := by
  decide +kernel

theorem p6138_s4d1 : derW 256 n1 j1 [h1 0, h1 1, h1 2, h1 3, h1 4, h1 5, h1 6] [h1 0, h1 1, h1 2]
    (fun a => decide (a < 256)) [(72, 108), (4, 192), (4, 128)] 8 = true := by
  decide +kernel

theorem p6138_s4w0 : (List.range 256).all (fun a =>
    cgK n0 [pwK n0 (h0 0) 2, h0 1, n0 (h0 0) (h0 2)] a ==
      bitW 256 (clIterK 256 n0 [1, 16, 32, 68, 92] 8) a) = true := by
  decide +kernel

theorem p6138_s4w1 : (List.range 256).all (fun a =>
    cgK n1 [pwK n1 (h1 0) 2, h1 1, n1 (h1 0) (h1 2)] a ==
      bitW 256 (clIterK 256 n1 [1, 16, 32, 68, 92] 8) a) = true := by
  decide +kernel

theorem p6138_s4q1 : derW 256 n1 j1 [1, 16, 32, 68, 92] [pwK n1 (h1 0) 2]
    (bitW 256 (clIterK 256 n1 [1, 16, 32, 68, 92] 8)) [(68, 92)] 8 = true := by
  decide +kernel

theorem p6138_s4r0 : s4RestW 256 n0 j0 h0 0 8 [1, 16, 32, 68, 92] = true := by
  decide +kernel

theorem p6138_s4r1 : s4RestW 256 n1 j1 h1 1 8 [1, 16, 32, 68, 92] = true := by
  decide +kernel

end CertificateChecks.KernelChengHeld.P

end

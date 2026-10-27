module

public import Certificates.Kernel.ChengHeld.PropsAut
public import Certificates.Data.Kernel.ChengHeldAutK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ChengHeldS2 CFSG.KC.ChengHeldP
open CFSG.OddStandard.ChengHeldData CertificateChecks.KernelChengHeld
open CertificateChecks.KernelChengHeld.S2 (IX0 IX1 IV0 IV1 AU0 AU1)

theorem p6138_bind01 : bAnd(bindW 256 9 CH0.T CH0.PL (IX0 0) (IV0 0),
    bindW 256 9 CH1.T CH1.PL (IX1 0) (IV1 0)) = true := by
  quickRfl

theorem p6138_rec0 : bAnd(autRecW 256 9 n0 CH0.T CH0.PL (imgL n0 j0 h0 (actRels 0 0)) (AU0 0),
    bAnd(autRecW 256 9 n0 CH0.T CH0.PL (imgL n0 j0 h0 (actRels 0 1)) (AU0 1),
      autRecW 256 9 n0 CH0.T CH0.PL (imgL n0 j0 h0 (actRels 0 2)) (AU0 2))) = true := by
  quickRfl

theorem p6138_rec1 : bAnd(autRecW 256 9 n1 CH1.T CH1.PL (imgL n1 j1 h1 (actRels 1 0)) (AU1 0),
    bAnd(autRecW 256 9 n1 CH1.T CH1.PL (imgL n1 j1 h1 (actRels 1 1)) (AU1 1),
      autRecW 256 9 n1 CH1.T CH1.PL (imgL n1 j1 h1 (actRels 1 2)) (AU1 2))) = true := by
  quickRfl

theorem p6138_cl0 : (clW 256 n0 [h0 0, h0 1, n0 (h0 3) (h0 4), h0 6] 16 &&
    clW 256 n0 [h0 0, h0 1, h0 2] 16 &&
    clW 256 n0 [h0 0, n0 (n0 (n0 (h0 3) (h0 4)) (h0 6)) (h0 2)] 16 && clW 256 n0 [h0 0] 16 &&
    clW 256 n0 [pwK n0 (h0 0) 2, h0 1, n0 (h0 0) (h0 2)] 16) = true := by
  decide +kernel

theorem p6138_aut0 : autRestW 256 n0 j0 h0 0 16 (fun k => aW 256 9 (AU0 k)) = true := by
  decide +kernel

theorem p6138_orb0 : orbW 256 n0 j0 h0 (aW 256 9 (AG0 0)) (h0 1) 16 = true := by
  decide +kernel

theorem p6138_g0 : gRestW 256 n0 j0 h0 0 16 (aW 256 9 (AG0 0)) = true := by
  decide +kernel

theorem p6138_cl1 : (clW 256 n1 [h1 0, h1 1, n1 (h1 3) (h1 4), h1 6] 16 &&
    clW 256 n1 [h1 0, h1 1, h1 2] 16 &&
    clW 256 n1 [h1 0, n1 (n1 (n1 (h1 3) (h1 4)) (h1 6)) (h1 2)] 16 && clW 256 n1 [h1 0] 16 &&
    clW 256 n1 [pwK n1 (h1 0) 2, h1 1, n1 (h1 0) (h1 2)] 16) = true := by
  decide +kernel

theorem p6138_aut1 : autRestW 256 n1 j1 h1 1 16 (fun k => aW 256 9 (AU1 k)) = true := by
  decide +kernel

theorem p6138_orb1 : orbW 256 n1 j1 h1 (aW 256 9 (AG1 0)) (h1 1) 16 = true := by
  decide +kernel

theorem p6138_g1 : gRestW 256 n1 j1 h1 1 16 (aW 256 9 (AG1 0)) = true := by
  decide +kernel

theorem p6138_cl2 : (clW 128 n2 [h2 0, h2 1, n2 (h2 3) (h2 4), h2 6] 16 &&
    clW 128 n2 [h2 0, h2 1, h2 2] 16 &&
    clW 128 n2 [h2 0, n2 (n2 (n2 (h2 3) (h2 4)) (h2 6)) (h2 2)] 16 &&
    clW 128 n2 [h2 0] 16) = true := by
  decide +kernel

theorem p6138_aut2 : autRestW 128 n2 j2 h2 2 16 (fun k => aW 128 8 (AU2 k)) = true := by
  decide +kernel

theorem p6138_orb2 : (orbW 128 n2 j2 h2 (aW 128 8 (AG2 0)) (h2 1) 16 &&
    orbW 128 n2 j2 h2 (aW 128 8 (AG2 0)) (h2 2) 16 &&
    orbW 128 n2 j2 h2 (aW 128 8 (AG2 0)) (h2 0) 16) = true := by
  decide +kernel

theorem p6138_g2 : gRestW 128 n2 j2 h2 2 16 (aW 128 8 (AG2 0)) = true := by
  decide +kernel

end CertificateChecks.KernelChengHeld.P

end

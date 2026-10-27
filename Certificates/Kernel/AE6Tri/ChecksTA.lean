module

public import Certificates.Data.Kernel.AE6Tri.DefsTA
public import Certificates.Kernel.AE6Tri.Data
public import Certificates.Kernel.AE6Tri.DataB
public import Certificates.Kernel.AE6Tri.DataTA
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6TriTA

open CFSG.KC.Enum CFSG.KC.AE6Tri CFSG.KD.AE6Tri CFSG.KD.AE6TA

theorem kTaL : lOK RG taLL taTau taEL taTP taTC taKw1 = true := by quickRfl

theorem kTaK : vOK taLL RG taKW taKI = true := by quickRfl

theorem kTaT : vOK taLL RG tg0 taTI = true := by quickRfl

theorem kTaS0 : vOK taLL RG tg0 (nthD taSI [] 0) = true := by quickRfl

theorem kTaS1 : vOK taLL (nthD dg [] 0) tg0 (nthD taSI [] 1) = true := by quickRfl

theorem kTaS2 : vOK taLL (nthD dg [] 1) tg0 (nthD taSI [] 2) = true := by quickRfl

theorem kTaS3 : vOKd taLL (nthD dg [] 1) (nthD delta [] 0) tg0 (nthD taSI [] 3) = true := by
  quickRfl

theorem kTaS4 : vOKd taLL (nthD dg [] 0) (nthD delta [] 1) tg0 (nthD taSI [] 4) = true := by
  quickRfl

theorem kTaS5 : vOKdd taLL (nthD dg [] 0) (nthD delta [] 1) (nthD delta [] 0) tg0
    (nthD taSI [] 5) = true := by quickRfl

theorem kTaB : invB RG ml taB = true := by quickRfl

theorem kTaP : tOK taLL (maskL taB) taPW taPO taPS taPM taTI taTW = true := by quickRfl

theorem kTaSrch0 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 0 30 = true := by
  quickRfl

theorem kTaSrch1 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 30 60 = true := by
  quickRfl

theorem kTaSrch2 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 60 90 = true := by
  quickRfl

theorem kTaSrch3 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 90 120 = true := by
  quickRfl

theorem kTaSrch4 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 120 150 = true := by
  quickRfl

theorem kTaSrch5 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 150 180 = true := by
  quickRfl

theorem kTaSrch6 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 180 210 = true := by
  quickRfl

theorem kTaSrch7 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 210 240 = true := by
  quickRfl

theorem kTaSrch8 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 240 270 = true := by
  quickRfl

theorem kTaSrch9 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 270 300 = true := by
  quickRfl

theorem kTaSrch10 : sOK taLL taTau 93 taB taPW taPO taPS taPM taSI taNodes 300 330 = true := by
  quickRfl

theorem kTaLen : Nat.ble (lenL taNodes) 330 = true := by quickRfl

end CertificateChecks.KernelAE6TriTA

end

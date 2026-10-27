module

public import Certificates.Kernel.AE6Q8.Cls
public import Certificates.Kernel.AE6Q8.Data
public import Certificates.Kernel.AE6Core.Chain
public import Certificates.Kernel.AE6Sm.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Sm

open CFSG.KS CFSG.KC.Enum CFSG.KS.SporSch.MOC
open CertificateChecks.KernelAE6Q8 CertificateChecks.KernelAE6Core

@[expose] noncomputable def nrZ : Nat := Nat.sub (SR.RO (Nat.succ SR.zc)) (SR.RO SR.zc)

@[expose] noncomputable def rlZ (d : Nat) : Nat := SR.RL (Nat.add (SR.RO SR.zc) d)

theorem ch517503x : xHdK 360 9 (mask 9) (360 * 9) SR.GS SR.GSI ZR.X ZR.XI ZR.XW ZR.nx = true := by
  decide +kernel

theorem ch517503cut : allN nrZ (cutK 360 9 (mask 9) (360 * 9) SC.BP 5 SC.LR SC.TR SC.TRI rlZ
    (fun _ => 0) (fun i => i) (fun _ => 0) ZR.X ZR.XI ZR.CT ZR.CP) = true := by
  decide +kernel

theorem ch517503nr : Nat.beq nrZ 240 = true := by decide +kernel

theorem ch517503nq : bAnd(Nat.beq ZR.ntw 4, Nat.beq ZR.nq 1120) = true := by decide +kernel

@[expose] noncomputable def pairB (b : Nat) : Bool := allBlk b (pairQK 360 9 (mask 9) (360 * 9)
    SC.BP 5 SC.LR SC.TR rlZ ZR.CT ZR.PQ ZR.QJ nrZ ZR.nq) 60

theorem ch517503p0 : pairB 0 = true := by decide +kernel

theorem ch517503p1 : pairB 60 = true := by decide +kernel

theorem ch517503p2 : pairB 120 = true := by decide +kernel

theorem ch517503p3 : pairB 180 = true := by decide +kernel

theorem ch517503tw : allN ZR.ntw (twinQK 360 9 (mask 9) (360 * 9) 5 SK.N SC.LR SC.TR PL.S
    ZR.QJ) = true := by
  decide +kernel

@[expose] noncomputable def subB (b : Nat) : Bool := allBlk b (subAK 360 9 (mask 9) (360 * 9)
    SC.BP 5 SK.N ZR.nx (SK.E (SR.RP SR.zc)) SC.LR SC.TR ZR.X ZR.XI ZR.QJ ZR.QA ZR.QW ZR.QP) 279

theorem ch517503s0 : subB 4 = true := by decide +kernel

theorem ch517503s1 : subB 283 = true := by decide +kernel

theorem ch517503s2 : subB 562 = true := by decide +kernel

theorem ch517503s3 : subB 841 = true := by decide +kernel

end CertificateChecks.KernelAE6Sm

end

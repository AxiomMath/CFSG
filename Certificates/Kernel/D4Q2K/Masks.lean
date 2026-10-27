module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Kernel.D4Q2K.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K

theorem ch709441mk0 : masksK D.pts D.frames.toList (D.MF) (0) 280 = true := by
  quickRfl

theorem ch709441mk1 : masksK D.pts D.frames.toList (D.MF) (280) 280 = true := by
  quickRfl

theorem ch709441mk2 : masksK D.pts D.frames.toList (D.MF) (560) 280 = true := by
  quickRfl

theorem ch709441mk3 : masksK D.pts D.frames.toList (D.MF) (840) 280 = true := by
  quickRfl

theorem ch709441mk4 : masksK D.pts D.frames.toList (D.MF) (1120) 280 = true := by
  quickRfl

theorem ch709441mk5 : masksK D.pts D.frames.toList (D.MF) (1400) 280 = true := by
  quickRfl

theorem ch709441mk6 : masksK D.pts D.frames.toList (D.MF) (1680) 280 = true := by
  quickRfl

theorem ch709441mk7 : masksK D.pts D.frames.toList (D.MF) (1960) 280 = true := by
  quickRfl

theorem ch709441mk8 : masksK D.pts D.frames.toList (D.MF) (2240) 280 = true := by
  quickRfl

theorem ch709441mk9 : masksK D.pts D.frames.toList (D.MF) (2520) 280 = true := by
  quickRfl

theorem ch709441mk10 : masksK D.pts D.frames.toList (D.MF) (2800) 280 = true := by
  quickRfl

theorem ch709441mk11 : masksK D.pts D.frames.toList (D.MF) (3080) 280 = true := by
  quickRfl

theorem ch709441mk12 : masksK D.pts D.frames.toList (D.MF) (3360) 280 = true := by
  quickRfl

theorem ch709441mk13 : masksK D.pts D.frames.toList (D.MF) (3640) 280 = true := by
  quickRfl

theorem ch709441mk14 : masksK D.pts D.frames.toList (D.MF) (3920) 280 = true := by
  quickRfl

theorem ch709441mk15 : masksK D.pts D.frames.toList (D.MF) (4200) 280 = true := by
  quickRfl

theorem ch709441inc : incK D.MF 4479 = true := by
  quickRfl

theorem ch709441mk_negBit :
    (!masksK D.pts D.frames.toList (fun j => Nat.xor (D.MF j) 1) 0 1) = true := by
  quickRfl

theorem ch709441mk_negShift :
    (!masksK D.pts D.frames.toList (fun j => D.MF (Nat.succ j)) 0 1) = true := by
  quickRfl

theorem ch709441inc_neg : (!incK (fun j => D.MF (Nat.sub j 1)) 4479) = true := by
  quickRfl

end CertificateChecks.KernelD4Q2K

end

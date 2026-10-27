module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Kernel.D4Q2K.Data
public import Certificates.Kernel.D4Q2K.DataS
public import Certificates.Kernel.D4Q2K.DataT
public import Certificates.Kernel.D4Q2K.DataA
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K CFSG.KC.Enum

theorem ch709441fp : fpK D.pts D.frames.toList DA.FP = true := by
  quickRfl

@[expose] noncomputable def cxSl (s : Nat) : Bool :=
  allBlk (Nat.mul 312 s) (fun t => bIf(Nat.blt t 4989, cxK DA.FP DA.XC DA.CX t 1, true)) 312

@[expose] noncomputable def apSl (s : Nat) : Bool :=
  apK D.pts D.MF DS.SF DT.TF DA.XC DA.CX DA.AP 4989 (Nat.mul 280 s) 280

#kc_each CertificateChecks.KernelD4Q2K.cxSl 0 16
#kc_each CertificateChecks.KernelD4Q2K.apSl 0 16

theorem cx_neg : (!cxK DA.FP DA.XC (fun k => Nat.xor (DA.CX k) 1) 0 1) = true := by
  quickRfl

theorem ap_neg :
    (!apK D.pts D.MF DS.SF DT.TF DA.XC DA.CX (fun j => Bool.rec (motive := fun _ => List Nat) (DA.AP j) [] (Nat.beq j 0)) 4989 0 1) =
      true := by
  quickRfl

end CertificateChecks.KernelD4Q2K

end

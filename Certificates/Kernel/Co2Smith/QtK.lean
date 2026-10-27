module

public import Certificates.Data.Kernel.Co2Smith.Pts
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Kernel.Co2Smith.Elems
public import Certificates.Kernel.Co2Smith.QtData
public import Certificates.Kernel.Co2Smith.CoxData
public import Certificates.Kernel.SporSch.Co2M.Seeds

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def mkRK (i : Nat) : Nat := wK LP (glMkRWord i)

@[expose] noncomputable def qtGenK (k : Nat) : Nat :=
  if k < 6 then (if k == 0 then zK else TP (k - 1)) else mkRK 16

@[expose] noncomputable def qtK : Bool :=
  commK (wK LP [11, 12]) zK &&
    (List.range 36).all (fun k => commK (wK LP [11, 12]) (mkRK k) == (k == 0 || k == 16 || k == 18)) &&
    eqK (mulV (mulV zK (mkRK 16)) zK) (mkRK 18) &&
    glQtLetters.all (fun e => e.2.all (· < 7) && eqK (wK qtGenK e.2) (wK LP [e.1]))

theorem qt_k : qtK = true := by decide +kernel

theorem qtFix_k : (bindVK (KernelSporSch.Co2M.PV 0) (QP 0) (CFSG.KC.Co1F2.trK 22 (mulV gaK zK)) &&
    fixCntK (QP 0) == 52) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith

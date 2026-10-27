module

public import Certificates.Kernel.Co2Smith.WDefs
public import CFSG.Sporadic.Co2Smith.GlNJInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def njGK (k : Nat) : Nat := wK LP glNJGw[k]!

@[expose] noncomputable def njGenK : Bool :=
  glNJGw.size == 3 && glNJGw.toList.all (fun w => w.all (· < 22)) && glNJTab.size == 3 &&
    glNJTw.length == 3 && glNJTw.all (· < 1024) &&
    commK (njGK 0) zK && commK (njGK 1) zK &&
    (List.range 3).all fun k => tabWK (njGK k) glNJTab[k]! &&
      tabWK (mulV (jcK glNJTw[k]!) (njGK k)) glNJTab[k]!

@[expose] noncomputable def njInjK : Bool :=
  (List.range 1024).all fun m => m == 0 || !eqK (jcK m) IDP

theorem njGen_k : njGenK = true := by decide +kernel

theorem njInj_k : njInjK = true := by decide +kernel

theorem njOm_k : glNJOmOK = true := by decide +kernel

end CertificateChecks.KernelCo2Smith

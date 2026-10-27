module

public import CFSG.Sporadic.Co2Smith.GlU62WeylInputs
public import Certificates.Kernel.Co2Smith.Elems

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def wgK (g : Nat) : Nat := [w1K, w2K, w3K, d0K, d1K].getD g 0

@[expose] noncomputable def weylK : Bool :=
  (List.range 5).all fun g => (List.range 18).all fun r => (List.range 4).all fun t =>
    decide ((glWAct g r t).1 < 18) && decide ((glWAct g r t).2 < 4) &&
      eqK (cjK (wgK g) (rootK r t)) (rootK (glWAct g r t).1 (glWAct g r t).2)

theorem weyl_k : weylK = true := by decide +kernel

theorem charts_k : glChartsOK = true := by decide +kernel

end CertificateChecks.KernelCo2Smith

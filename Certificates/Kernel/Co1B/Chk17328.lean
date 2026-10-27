module

public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.TabCo1Reps
public import Certificates.Data.Kernel.Co1BFix
public import Certificates.Data.Kernel.Co1F2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C17328

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.HardMathSupport.Dickson.I271.TabCo1

@[expose] def packRows : List Nat → Nat
  | [] => 0
  | r :: rs => r + 2 ^ 24 * packRows rs

@[expose] noncomputable def D1K : Nat := packRows repD1.toList

theorem xD1 : Nat.beq (fixTabK (trK 24 D1K) CV.F 117) 60 = true := by quickRfl

end CertificateChecks.KernelCo1B.C17328

end

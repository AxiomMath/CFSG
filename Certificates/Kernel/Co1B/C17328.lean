module

public import Certificates.Kernel.Co1B.Chk17328
public import Certificates.Kernel.Co1B.C2041

public section

namespace CertificateChecks.KernelCo1B.C17328

open CFSG.KC.Co1F2 CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Dickson.I271.TabCo1

theorem repD1_eq : repD1 = unpackR 24 D1K := by decide +kernel

theorem fixD1 : xFixCount certVecs (unpackR 24 D1K) = CFSG.KC.Co1B.fixTabK (trK 24 D1K) CV.F 117 :=
  xFix_eq rfl

open Certificates in
open CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Dickson.I271.TabCo1 in
theorem c17328 : xFixCount certVecs repD1 = 60 := by
  rw [repD1_eq, fixD1, Nat.eq_of_beq_eq_true xD1]

end CertificateChecks.KernelCo1B.C17328

end

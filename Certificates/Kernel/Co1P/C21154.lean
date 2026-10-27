module

public import Certificates.Kernel.Co1P.Q2Glue
public import Certificates.Kernel.Co1P.Chk21154S
public import Certificates.Kernel.Co1P.Chk21154T0
public import Certificates.Kernel.Co1P.Chk21154T1
public import Certificates.Kernel.Co1P.Chk21154L

public section

namespace CertificateChecks.KernelCo1P

open CFSG.Sporadic.Co1Patterson.Native

theorem q2_0 : q2Check 0 = true :=
  q2Check_of (by decide) q2_small0 (fun f hf => Q2T0.all f hf) (fun c hc => Q2L0.all c hc)

theorem q2_1 : q2Check 1 = true :=
  q2Check_of (by decide) q2_small1 (fun f hf => Q2T1.all f hf) (fun c hc => Q2L1.all c hc)

theorem q2_2 : q2Check 2 = true :=
  q2Check_of (by decide) q2_small2 (fun f hf => Q2T2.all f hf) (fun c hc => Q2L2.all c hc)

theorem q2_3 : q2Check 3 = true :=
  q2Check_of (by decide) q2_small3 (fun f hf => Q2T3.all f hf) (fun c hc => Q2L3.all c hc)

open Certificates in
theorem c21154 : CFSG.Sporadic.Co1Patterson.Native.q2Check 0 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.q2Check 1 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.q2Check 2 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.q2Check 3 = true := ⟨q2_0, q2_1, q2_2, q2_3⟩

end CertificateChecks.KernelCo1P

end

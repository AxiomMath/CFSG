module

public import Certificates.Kernel.Co1P.Q2Glue
public import Certificates.Kernel.Co1P.Chk21155S
public import Certificates.Kernel.Co1P.Chk21155T
public import Certificates.Kernel.Co1P.Chk21155L

public section

namespace CertificateChecks.KernelCo1P

open CFSG.Sporadic.Co1Patterson.Native

theorem q2_4 : q2Check 4 = true :=
  q2Check_of (by decide) q2_small4 (fun f hf => Q2T4.all f hf) (fun c hc => Q2L4.all c hc)

theorem q2_5 : q2Check 5 = true :=
  q2Check_of (by decide) q2_small5 (fun f hf => Q2T5.all f hf) (fun c hc => Q2L5.all c hc)

theorem q2_6 : q2Check 6 = true :=
  q2Check_of (by decide) q2_small6 (fun f hf => Q2T6.all f hf) (fun c hc => Q2L6.all c hc)

open Certificates in
theorem c21155 : CFSG.Sporadic.Co1Patterson.Native.q2Check 4 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.q2Check 5 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.q2Check 6 = true := ⟨q2_4, q2_5, q2_6⟩

end CertificateChecks.KernelCo1P

end

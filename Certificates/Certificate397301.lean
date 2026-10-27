module

public import Certificates.Data.AEOrbit
import Certificates.Kernel.AEOrbit.Checks
import CFSG.Certificates.Kernel.AEOrbitSound

public section

namespace Certificates

open CertificateChecks.KernelAEOrbit

theorem certificate397301 : AEOrbit.check () = true :=
  CFSG.KC.AEOrbitK.check_of (List.all_eq_true.1 c397301sign5 · · |> of_decide_eq_true)
    (List.all_eq_true.1 c397301sign6 · · |> of_decide_eq_true)
    ((beq_iff_eq.1 c397301ct5).symm ▸ c397301k5) ((beq_iff_eq.1 c397301ct6).symm ▸ c397301k6)
    (List.all_eq_true.1 c397301lt5 · · |> of_decide_eq_true)
    (List.all_eq_true.1 c397301lt6 · · |> of_decide_eq_true) c397301cov5 c397301cov6

end Certificates

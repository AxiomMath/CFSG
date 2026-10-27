module

public import Certificates.Data.SmithL6Orbit
public import Certificates.Data.Kernel.SmithL6K
import Certificates.Kernel.SmithL6K.GlueO

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithL6 in
theorem certificate38604 :
    K.Reach 1395 1953 (· == 0) (fun k u v => planeImg k u == v) ∧
    K.Reach 1395 1953 (fun j => j == dRoot (meetCard 0 j))
      (fun p u v => planeImg p 0 == 0 && meetCard 0 u == meetCard 0 v && planeImg p u == v) ∧
    (List.range 512).countP (fun v => uCls uSums v == 1) = 49 ∧
    (List.range 512).countP (fun v => uCls uSums v == 2) = 294 ∧
    (List.range 512).countP (fun v => uCls uSums v == 3) = 168 ∧
    K.Reach 512 1953 (fun v => v == uRoot uSums (uCls uSums v))
      (fun p u v => planeImg p 0 == 0 && uCls uSums u == uCls uSums v &&
        CFSG.SmithE.applyCols (ucols p) u == v) :=
  ⟨KernelSmithL6K.trans_reach, KernelSmithL6K.plane_reach, KernelSmithL6K.u_counts.1,
    KernelSmithL6K.u_counts.2.1, KernelSmithL6K.u_counts.2.2, KernelSmithL6K.u_reach⟩

end Certificates

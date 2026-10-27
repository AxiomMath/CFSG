module

public import Certificates.Data.Kernel.Cert690.SqPglT
public import Certificates.Kernel.Cert690.SqPgl4Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPgl

open CFSG.KC.C690

set_option maxHeartbeats 0 in
theorem recNegT : (Xs.take 1).all (fun X => pqRecOK Fr Ar (X.1, X.2.1, X.2.2.1, X.2.2.2.1,
    X.2.2.2.2.1, X.2.2.2.2.2.1, Nat.xor X.2.2.2.2.2.2.1 1, X.2.2.2.2.2.2.2)) = false := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem innNeg : (Xs.take 1).all (fun X => pqInnOK X.2.1 X.2.2.1 X.2.2.2.2.2.2.1
    (Nat.xor (pqE X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 0) 2)
    (pqInvQ (Nat.xor (pqE X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 0) 2)) 0) = false := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem csNeg : (Xs.take 1).all (fun X => pqCs I0 (X.1, X.2.1, X.2.2.1, X.2.2.2.1, X.2.2.2.2.1,
    X.2.2.2.2.2.1, X.2.2.2.2.2.2.1, [])) = false := by
  decide +kernel

end CertificateChecks.KernelC690.SqPgl

end

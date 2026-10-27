module

public import Certificates.Kernel.Co1Surj.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SurjNeg

open CFSG.KC.SurjK CFSG.KC.SurjChain CFSG.KC.M1F2 CertificateChecks.KernelCo1Surj
open CFSG.KS (lget)
open CFSG.Sporadic.Bridge.SurjD.Native

theorem words : Bool.not (wordsK IT.chars IW.W.tail) = true := by quickRfl

theorem surj : Bool.not (Nat.beq (wordRF 24 (imgF Ims ImsI) (Ls.getD 0 []))
    CertificateChecks.KernelVec.Co1.NB) = true := by quickRfl

theorem rel : Bool.not (co1Spec.rels.all (fun r => r.all (fun l => decide (l.1 < 8)) &&
    Nat.beq (wordRF 24 (imgF (lget Ims 1 :: lget Ims 0 :: Ims.drop 2) ImsI) (r.map letterOf))
      (idF 24))) = true := by quickRfl

theorem inv : Bool.not (Nat.beq (mulF 24 (lget Ims 0) (lget ImsI 1)) (idF 24)) = true := by quickRfl

end CertificateChecks.KernelCo1SurjNeg

end

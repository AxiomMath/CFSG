module

public import Certificates.Kernel.A45Cls.Cls2
public import Certificates.Data.Kernel.A45Cls.Pock
public import Certificates.Kernel.A45Cls.Cls

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls

@[expose] noncomputable def yP (k : ℕ) : ℕ := wordK 45 6 KA.G (yW.getD k [])

theorem binds2 :
    YB.G 0 = KA.G 0 ∧ YB.G 1 = KA.G 1 ∧ YB.G 2 = KA.G 2 ∧
    YC.G 0 = KA.G 0 ∧ YC.G 1 = KA.G 1 ∧ YC.G 2 = KA.G 2 ∧
    YB.T YB.r0 = yP 0 ∧ YC.T YC.r0 = yP 2 ∧
    bindWs 45 6 3 KA.G CB.G cbW 0 = true ∧ bindWs 45 6 3 KA.G CC.G ccW 0 = true := by
  decide +kernel

theorem yWords : bindWs 45 6 2 KA.G yP yW 0 = true := by decide +kernel

theorem ids2 : CB.T 0 = pidn 45 6 ∧ CC.T 0 = pidn 45 6 := by decide +kernel

theorem yFacts : allN 4 (fun k => isIdK 45 6 (pcomp 45 6 (mask 6) (yP k)
      (pcomp 45 6 (mask 6) (yP k) (yP k)))) = true ∧
    allN 2 (fun k => eq22 45 6 (mask 6) (yP k) (KB.T KB.r0) (KB.T KB.r0) (yP k)) = true ∧
    allN 2 (fun k => eq22 45 6 (mask 6) (yP (k + 2)) (K540.T K540.r0) (K540.T K540.r0)
      (yP (k + 2))) = true ∧
    allN 3 (fun k => eq22 45 6 (mask 6) (CB.G k) (yP 0) (yP 0) (CB.G k)) = true ∧
    allN 4 (fun k => eq22 45 6 (mask 6) (CC.G k) (yP 2) (yP 2) (CC.G k)) = true := by
  decide +kernel

theorem f6 : f6K 45 6 CB.N CB.T (KB.T KB.r0) (yP 1) = true ∧
    f6K 45 6 CC.N CC.T (K540.T K540.r0) (yP 3) = true := by
  decide +kernel

end CertificateChecks.KernelA45

end

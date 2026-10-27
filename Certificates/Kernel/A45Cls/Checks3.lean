module

public import Certificates.Kernel.A45Cls.Checks
public import Certificates.Data.Kernel.A45Cls.Pock
public import Certificates.Data.OmegaTypes

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def kaN (j : ℕ) : ℕ := (cOf ((Certificates.OmegaTypes.kaList ()).getD j 1)).1

@[expose] noncomputable def kbN (j : ℕ) : ℕ :=
  (cOf ((Certificates.OmegaPk.kbList (Certificates.OmegaPk.g0 ())
    (Certificates.OmegaTypes.kaList ())).getD j 1)).1

theorem pockA : allN CA.N (fun i => strictB (CA.T i) fun u =>
    pockD 45 6 24 kaN kbN (KA.T KA.r0) u && pockE 45 6 24 kaN kbN (KA.T KA.r0) u) = true := by
  decide +kernel

theorem pockT : exN 24 (fun j => Nat.beq (kaN j) (KA.T KA.r0)) = true ∧
    allN 24 (fun m => !isInvK 45 6 (kbN m) || Nat.beq (kbN m) (KA.T KA.r0)) = true := by
  decide +kernel

end CertificateChecks.KernelA45

end

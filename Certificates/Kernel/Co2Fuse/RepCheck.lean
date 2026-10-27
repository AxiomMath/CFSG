module

public import Certificates.Kernel.Co2Fuse.RepData
public import Certificates.Data.Kernel.Co2Fuse
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Fuse

open CFSG.KC.Co2InvS CFSG.KC.Co2Fuse CertificateChecks.KernelSpor.Co2Syl

@[expose] def LR : Nat := 288083878177

theorem repLabs : ∀ i < 10,
    Nat.beq (labY CR (RP 0) (RP i) (Nat.mul 3 i)) (fld(LR, Nat.mul 4 i, 15)) = true := by
  kc_cover 10

@[expose] noncomputable def flipR (T : Nat → Nat) (j i : Nat) (x : Nat) : Nat :=
  Nat.xor (T x) (nIf(Nat.beq x j, Nat.shiftLeft 1 i, 0))

theorem neg_repRank : notK (Nat.beq (labY (flipR CR 29 484) (RP 0) (RP 9) 27) 4) = true := by
  quickRfl
theorem neg_repCert : notK (Nat.beq (labY (flipR CR 12 462) (RP 0) (RP 4) 12) 3) = true := by
  quickRfl
theorem neg_repSwap : notK (Nat.beq (labY CR (RP 0) (RP 9) 12) 4) = true := by quickRfl
theorem neg_repSwap' : notK (Nat.beq (labY CR (RP 0) (RP 4) 27) 3) = true := by quickRfl

end CertificateChecks.KernelSpor.Co2Fuse

end

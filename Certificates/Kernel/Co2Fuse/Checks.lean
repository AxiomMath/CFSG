module

public import Certificates.Kernel.Co2Fuse.BlkA
public import Certificates.Kernel.Co2Fuse.BlkB
public import Certificates.Kernel.Co2Fuse.BlkC
public import Certificates.Kernel.Co2Fuse.BlkD
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.Co2Fuse

open CFSG.KC.Co2InvS CFSG.KC.Co2Fuse CertificateChecks.KernelSpor.Co2Syl

theorem fuse_slices {F : Nat → Bool} {m : Nat}
    (h : ∀ s < m, ∀ t < 256, F (Nat.add (256 * s) t) = true) : ∀ b < 256 * m, F b = true := by
  intro b hb
  have e : Nat.add (256 * (b / 256)) (b % 256) = b := Nat.div_add_mod b 256
  rw [← e]
  exact h (b / 256) (by omega) (b % 256) (Nat.mod_lt _ (by norm_num))

theorem fuses : ∀ b < 1024, fuseB E3.CF PT CI CA (RP 0) (RP 2) CNT 65536 b = true :=
  fuse_slices (m := 4) fun s hs => by
    interval_cases s
    exacts [fusea, fuseb, fusec, fused]

theorem totC9 : Nat.beq (cntTotal CNT 0 16) 32 = true := by quickRfl
theorem totCB9 : Nat.beq (cntTotal CNT 1 16) 68 = true := by quickRfl
theorem totB9C : Nat.beq (cntTotal CNT 2 16) 36 = true := by quickRfl

end CertificateChecks.KernelSpor.Co2Fuse

end

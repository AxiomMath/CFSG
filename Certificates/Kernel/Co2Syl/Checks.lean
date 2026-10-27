module

public import Certificates.Kernel.Co2Syl.Rec1a
public import Certificates.Kernel.Co2Syl.Rec1b
public import Certificates.Kernel.Co2Syl.Rec1c
public import Certificates.Kernel.Co2Syl.Rec1d
public import Certificates.Kernel.Co2Syl.Rec1e
public import Certificates.Kernel.Co2Syl.Rec1f
public import Certificates.Kernel.Co2Syl.Rec1g
public import Certificates.Kernel.Co2Syl.Rec1h
public import Certificates.Kernel.Co2Syl.Rec3a
public import Certificates.Kernel.Co2Syl.Rec3b
public import Certificates.Kernel.Co2Syl.Rec3c
public import Certificates.Kernel.Co2Syl.Rec3d
public import Certificates.Kernel.Co2Syl.Rec4a
public import Certificates.Kernel.Co2Syl.Rec4b
public import Certificates.Kernel.Co2Syl.Rec5
public import Certificates.Kernel.Co2Syl.Rec6
public import Certificates.Kernel.Co2Syl.Rec8
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2Syl

theorem slices {F : Nat → Bool} {m : Nat} (h : ∀ s < m, ∀ t < 256, F (Nat.add (256 * s) t) = true) :
    ∀ b < 256 * m, F b = true := by
  intro b hb
  have e : Nat.add (256 * (b / 256)) (b % 256) = b := Nat.div_add_mod b 256
  rw [← e]
  exact h (b / 256) (by omega) (b % 256) (Nat.mod_lt _ (by norm_num))

theorem blks1 : ∀ b < 2048, blkT E1.CF G1 (RP 1) (RP 0) CNT1 131072 b = true :=
  slices (m := 8) fun s hs => by
    interval_cases s
    exacts [blk1a, blk1b, blk1c, blk1d, blk1e, blk1f, blk1g, blk1h]

theorem blks3 : ∀ b < 1024, blkT E3.CF G3 (RP 3) (RP 0) CNT3 65536 b = true :=
  slices (m := 4) fun s hs => by
    interval_cases s
    exacts [blk3a, blk3b, blk3c, blk3d]

theorem blks4 : ∀ b < 512, blkT E4.CF G4 (RP 4) (RP 0) CNT4 32768 b = true :=
  slices (m := 2) fun s hs => by
    interval_cases s
    exacts [blk4a, blk4b]

theorem blks5 : ∀ b < 256, blkT E5.CF G5 (RP 5) (RP 0) CNT5 16384 b = true := blk5
theorem blks6 : ∀ b < 256, blkT E6.CF G6 (RP 6) (RP 0) CNT6 16384 b = true := blk6
theorem blks8 : ∀ b < 256, blkT E8.CF G8 (RP 8) (RP 0) CNT8 16384 b = true := blk8

end CertificateChecks.KernelSpor.Co2Syl

end

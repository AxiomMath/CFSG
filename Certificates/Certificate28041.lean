module

public import CFSG.Certificates.Kernel.EvenBN.Ops2Sound
public import Certificates.Kernel.EvenBN.K28041
public import Certificates.Kernel.EvenBN.Th8Bind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch28041

open CFSG.SectionRank.Native CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Ops2 CertificateChecks.Th8
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

theorem decA : (ops2 248).decode thOrd8Data.seedA = unpackR 248 A.M := by
  change CFSG.Sporadic.SmallF2.Native.rowsOfPayload 248 CertificateChecks.KernelLC.thSeedA = _
  rw [SA.eq, bind_sound SA.bind]
  rfl

theorem decB : (ops2 248).decode thOrd8Data.seedB = unpackR 248 B.M := by
  change CFSG.Sporadic.SmallF2.Native.rowsOfPayload 248 CertificateChecks.KernelLC.thSeedB = _
  rw [SB.eq, bind_sound SB.bind]
  rfl

theorem regs (a b : Nat) : ((ops2 248).run thOrd8Data.prog ((ops2 248).initRegs (unpackR 248 a)
    (unpackR 248 b) thOrd8Data.nregs))[11]! = unpackR 248 (r11 a b) := by
  rw [run11, CFSG.KC.Ops2.pow_three', CFSG.KC.Ops2.pow_two']
  simp only [mul_unpack]
  rfl

theorem pow8 (a b : Nat) : (ops2 248).pow (unpackR 248 (r11 a b)) 8 = unpackR 248 (x8 a b) := by
  rw [CFSG.KC.Ops2.pow_eight']
  simp only [mul_unpack]
  rfl

theorem pow4 (a b : Nat) : (ops2 248).pow (unpackR 248 (r11 a b)) 4 = unpackR 248 (x4 a b) := by
  rw [CFSG.KC.Ops2.pow_four']
  simp only [mul_unpack]
  rfl

theorem moves4 : ((List.range 248).any fun j =>
    (vmF 248 (x4 A.M B.M) (1 <<< 0)).testBit j != (1 <<< 0 : Nat).testBit j) = true := k4

theorem ord8 : ord8OK (ops2 248) thOrd8Data 11 0 = true := by
  unfold ord8OK
  simp only [decA, decB, regs, pow8, pow4, one_unpack, vne_unpack, eq_unpack (d := 248) k8,
    moves4, Bool.and_true]
  decide

end CertificateChecks.Batch28041

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P CFSG.SectionRank.Native in
theorem certificate28041 : ord8OK (ops2 248) thOrd8Data 11 0 = true := CertificateChecks.Batch28041.ord8

end Certificates

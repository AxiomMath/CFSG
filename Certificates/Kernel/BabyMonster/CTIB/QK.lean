module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQAlg
public import Certificates.Kernel.BabyMonster.CTIB.CosetQStep
public import Certificates.Kernel.BabyMonster.CTIB.CosetQData
public import Certificates.Data.CFSGNative.CTIB.Lift
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelBM.CTIB.QK

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.Monster.B.CTIB.Native CertificateChecks.KernelBM.CTIB
  CertificateChecks.KernelBM.CTIB.CosetQ

theorem lo_eq : LOq = loOf (gArr ()) := Nat.eq_of_beq_eq_true (by quickRfl)

theorem symG : SymG (gArr ()) := by
  unfold SymG
  decide +kernel

theorem mulQ_eq (a b : ℕ) : mulQ LOq a b = qmul (gArr ()) a b := by
  rw [lo_eq, mulQ_loOf _ symG]

theorem autQ_eq (A n : ℕ) : autQ LOq A n = autApply (gArr ()) (arrOf A) n := by
  rw [lo_eq, autQ_loOf _ symG]

theorem qmul_mod (G : Array ℕ) (a b : ℕ) : qmul G a b % 2 ^ 22 = (a ^^^ b) % 2 ^ 22 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < 22
  · rw [decide_eq_true hi, Bool.true_and, Bool.true_and, qmul_bit G a b hi, Nat.testBit_xor]
  · rw [decide_eq_false hi, Bool.false_and, Bool.false_and]

end CertificateChecks.KernelBM.CTIB.QK

end

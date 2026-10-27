module

public import Certificates.Kernel.B433Alt.StOK
public import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Kernel.B433Alt.St.S0
public import Certificates.Kernel.B433Alt.St.S1
public import Certificates.Kernel.B433Alt.St.S2
public import Certificates.Kernel.B433Alt.St.S3
public import Certificates.Kernel.B433Alt.St.S4
public import Certificates.Kernel.B433Alt.St.S5
public import Certificates.Kernel.B433Alt.St.S6
public import Certificates.Kernel.B433Alt.St.S7
public import Certificates.Kernel.B433Alt.St.S8
public import Certificates.Kernel.B433Alt.St.S9
public import Certificates.Kernel.B433Alt.St.S10
public import Certificates.Kernel.B433Alt.St.S11
public import Certificates.Kernel.B433Alt.St.S12
public import Certificates.Kernel.B433Alt.St.S13
public import Certificates.Kernel.B433Alt.St.S14
public import Certificates.Kernel.B433Alt.St.S15

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A

#kc_forall_tree st_all (fun r => CFSG.KD.B4A.stOK r = true) 5965 CFSG.KD.B4A.st

section
variable (LP RD RW PW RJ : Nat → Nat)

theorem sN_eq (v : Nat) (k : Nat → Nat) : sN v k = k v := by cases v <;> rfl

theorem foldRange_succ (a k S : Nat) :
    foldRange LP RD RW PW RJ a (k + 1) S =
      foldRange LP RD RW PW RJ (a + 1) k (foldStep LP RD RW PW RJ a S) :=
  sN_eq _ _

theorem foldRange_add (a n m S : Nat) :
    foldRange LP RD RW PW RJ a (n + m) S =
      foldRange LP RD RW PW RJ (a + n) m (foldRange LP RD RW PW RJ a n S) := by
  induction n generalizing a S with
  | zero => rw [Nat.zero_add, Nat.add_zero]; rfl
  | succ n ih =>
    rw [Nat.add_right_comm, foldRange_succ, ih, foldRange_succ, Nat.add_right_comm, Nat.add_assoc]

theorem foldRange_of_steps (SS : Nat → Nat) (n : Nat)
    (h : ∀ r < n, foldOK LP RD RW PW RJ SS r = true) :
    foldRange LP RD RW PW RJ 0 n (SS 0) = SS n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldRange_add, ih (fun r hr => h r (by omega)), Nat.zero_add]
    exact Nat.eq_of_beq_eq_true (h n (by omega))

end

theorem st_fold : foldRange CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW
    CFSG.KD.B4A.RJ 0 5965 1 = 0x3c0fffffffffffffff := by
  have h0 : CFSG.KD.B4A.SS 0 = 1 := by decide +kernel
  have h1 : CFSG.KD.B4A.SS 5965 = 0x3c0fffffffffffffff := by decide +kernel
  rw [← h0, ← h1]
  exact foldRange_of_steps _ _ _ _ _ _ _ st_all

end CertificateChecks.KernelB433

end

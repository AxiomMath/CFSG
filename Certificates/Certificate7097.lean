module

public import Certificates.Data.A7Fano
import Certificates.Kernel.Misc.A7Cnt
import CFSG.Certificates.Kernel.Misc.A7CntSound

public section

namespace Certificates

open CertificateChecks.KernelA7Cnt CFSG.KC.A7Cnt in
open Equiv CFSG.A7Fano in
open scoped Pointwise in
theorem certificate7097 :
    (∀ g : Perm (Fin 7), Perm.sign g = 1 → g • fano1 = fano1 ∨ g • fano2 = fano2 ∨
      ∃ i : Fin 7, ∃ j : Fin 3, (g * cyc7 ^ (i : ℕ) * dbl7 ^ (j : ℕ)) ^ 5 = 1 ∧
        g * cyc7 ^ (i : ℕ) * dbl7 ^ (j : ℕ) ≠ 1) ∧
    (stabSet fano1).card = 168 ∧ (stabSet fano2).card = 168 ∧
    (∀ i, Perm.sign (reps1 i) = 1) ∧ (∀ i j, i ≠ j → ((reps1 i)⁻¹ * reps1 j) • fano1 ≠ fano1) ∧
    (∀ j : Fin 15, j ≠ 0 → fixCount fano1 reps1 j ≤ 3) ∧
    (∀ σ : Perm (Fin 7), σ.cycleType = {3} → normCount σ = 72) :=
  ⟨c1_of c1K_true hLK_true, (stK_eq f1_img).symm.trans (Nat.eq_of_beq_eq_true stK_1),
    (stK_eq f2_img).symm.trans (Nat.eq_of_beq_eq_true stK_2), (reps_of repK_true).1,
    (reps_of repK_true).2, fix_of repK_true fxK_true, norm_of (Nat.eq_of_beq_eq_true normK_72)⟩

end Certificates

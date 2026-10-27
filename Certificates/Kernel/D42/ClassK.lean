module

public import Certificates.Kernel.OmegaEight.Arr3009K

public section

namespace CertificateChecks.KernelD42

open CertificateChecks.KernelO8

@[expose] noncomputable def noFixUp (P : Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => ih && !Nat.beq (at9 P (i + 120)) (i + 120)) n

theorem noFixUp_spec {P : Nat} : ∀ {n : Nat}, noFixUp P n = true →
    ∀ i < n, at9 P (i + 120) ≠ i + 120
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    change (noFixUp P n && !Nat.beq (at9 P (n + 120)) (n + 120)) = true at h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact noFixUp_spec h.1 i hi
    · exact Nat.ne_of_beq_eq_false h.2

theorem kC2Fix : Nat.beq (at9 (mainK 1) 8) 8 = true := by decide +kernel

theorem kC2NoFix : noFixUp (mainK 1) 240 = true := by decide +kernel

end CertificateChecks.KernelD42

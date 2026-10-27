module

public import Certificates.Kernel.CoPair.S64
public import CFSG.Certificates.Kernel.CoPairSound
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelCoPair

open CFSG.KC.CoPair CFSG.Monster.Existence.CoPair.Native

@[expose] noncomputable def S64D : OrbData := ⟨MX, MY, TX, TY, S64.P, S64.E, 10⟩

theorem s64chunks : ∀ k < 46, allR (1000 * k) 1000 s64Pt = true := by
  intro k hk
  interval_cases k
  exacts [s64c0, s64c1, s64c2, s64c3, s64c4, s64c5, s64c6, s64c7, s64c8, s64c9, s64c10, s64c11,
    s64c12, s64c13, s64c14, s64c15, s64c16, s64c17, s64c18, s64c19, s64c20, s64c21, s64c22, s64c23,
    s64c24, s64c25, s64c26, s64c27, s64c28, s64c29, s64c30, s64c31, s64c32, s64c33, s64c34, s64c35,
    s64c36, s64c37, s64c38, s64c39, s64c40, s64c41, s64c42, s64c43, s64c44, s64c45]

theorem s64_ok : orbOK xWordN yWordN 64 46575 S64D = true :=
  orbOK_intro rowsX rowsY tabX tabY (by decide) (Nat.eq_of_beq_eq_true s64seed)
    (all_of_allR (all_of_chunks s64chunks) s64c46)

end CertificateChecks.KernelCoPair

end

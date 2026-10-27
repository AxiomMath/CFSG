module

public import Certificates.Kernel.Co1M.C25050K
public import Certificates.Kernel.Co1M.C10072T

public section

namespace CertificateChecks.KernelCo1M

open CFSG.EvenSporadicStandard.TwoB.MW3 CFSG.Sporadic.Co1.Module.Odd CFSG.Sporadic.Co1.OddNative
  CFSG.KC.Co1F2

theorem c25050_regs : regsRowsM = runRows (cmRP3.map (unpackRK 24)).toArray extraLines := by
  have h : ∀ (i : Array (Array ℕ)) (p q : List (List (ℕ × ℕ))),
      runRows i (p ++ q) = runRows (runRows i p) q := fun _ _ _ => List.foldl_append ..
  rw [regsRowsM, progM, h, ← regsRows3, cm_regs3]
  rfl

open Certificates in
open CFSG.EvenSporadicStandard.TwoB.MW3 in
theorem c25050 :
    commOK = true := by
  rw [commOK_eq_on, c25050_regs, cm_rr27]
  exact c25050_chk

end CertificateChecks.KernelCo1M

end

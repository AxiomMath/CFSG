module

public import CFSG.Certificates.Kernel.CertF8.Sound9640
public import Certificates.Kernel.CertF8.Syl9640Data
import Certificates.Kernel.CertF8.Syl9640Rows
import Certificates.Kernel.CertF8.Syl9640Comm
import Certificates.Kernel.CertF8.Glue9641
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace Certificates.Kernel.CertF8.C9640

open CFSG.KC.CertF8 CFSG.KC.CertF8.S9640 CFSG.KC.Misc.Clos CFSG.AGLEmbedding.ChevOuterD48
  CFSG.Open

#kc_forall_chunks rowsC
  (fun k => CFSG.KC.Misc.Clos.allR (Nat.mul 27 k) 27
    (CFSG.KC.CertF8.S9640.rowAt CFSG.KC.CertF8.S9640.T) = true) 27
  CFSG.KC.CertF8.S9640.ch9640r.c 1

#kc_forall_chunks commC
  (fun k => CFSG.KC.Misc.Clos.allR (Nat.mul 81 (Nat.mod k 9)) 81
    (CFSG.KC.CertF8.S9640.repAt CFSG.KC.CertF8.S9640.T (Nat.div k 9)) = true) 72
  CFSG.KC.CertF8.S9640.ch9640c.c 1

theorem rows : ∀ j < 729, rowAt T j = true :=
  forall_of_chunks 27 27 _ rowsC

theorem reps : ∀ q < 8, ∀ j < 729, repAt T q j = true := by
  intro q hq j hj
  have h := commC (9 * q + j / 81) (by change 9 * q + j / 81 < 72; omega)
  have e1 : Nat.mod (9 * q + j / 81) 9 = j / 81 := by
    change (9 * q + j / 81) % 9 = j / 81
    omega
  have e2 : Nat.div (9 * q + j / 81) 9 = q := by
    change (9 * q + j / 81) / 9 = q
    omega
  rw [e1, e2, allR_iff] at h
  exact h j (by change 81 * (j / 81) ≤ j; omega) (by change j < 81 * (j / 81) + 81; omega)

theorem facts9640 : Nat.card sylowGroup = 3 ^ 6 ∧
    ∀ E : Subgroup (GL (Fin 8) GF512), E ≤ sylowGroup → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 2 :=
  sound9640 C9641.ch9641One (fun k _ => C9641.codeA_letterArr k) rows reps ch9640g

end Certificates.Kernel.CertF8.C9640

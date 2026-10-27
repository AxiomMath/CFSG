module

public import Certificates.Kernel.Co1M.Base10077
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KC.TreeK

theorem ty77_chk : treeOK (actV YT77) 2 12 om77 T77Y = true := by quickRfl

theorem ty77 : (treePts (actV YT77) 2 om77 T77Y).1.Nodup ∧
    (treePts (actV YT77) 2 om77 T77Y).1.length = 4095 ∧
    ∀ x ∈ (treePts (actV YT77) 2 om77 T77Y).1, Reach (actV YT77) 2 om77 x := by
  obtain ⟨h1, h2, h3⟩ := treeOK_sound ty77_chk
  have hl : T77Y.length = 4094 := Nat.eq_of_beq_eq_true (by quickRfl)
  exact ⟨h1, by rw [h2, hl], h3⟩

end CertificateChecks.KernelCo1M

end

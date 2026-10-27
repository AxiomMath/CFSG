module

public import Certificates.Kernel.Co1M.Base10077
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KC.TreeK CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT

theorem uni77_chk : allN 6 (fun k => uniK (mulF 24 (mulF 24 QP77 (getL 0 SR77 k)) QIP77)) = true := by
  quickRfl

theorem uni77 : ∀ k < 6, ∀ i < 24,
    (∀ j < i, (fget (mulF 24 (mulF 24 QP77 (getL 0 SR77 k)) QIP77) i 24).testBit j = false) ∧
      (fget (mulF 24 (mulF 24 QP77 (getL 0 SR77 k)) QIP77) i 24).testBit i = true :=
  fun k hk => uni_spec (allN_true uni77_chk k hk)

theorem ts77_chk : treeOK (actV ST77) 6 11 GW77 T77S = true := by quickRfl

theorem ts77 : (treePts (actV ST77) 6 GW77 T77S).1.Nodup ∧
    (treePts (actV ST77) 6 GW77 T77S).1.length = 2048 ∧
    ∀ x ∈ (treePts (actV ST77) 6 GW77 T77S).1, Reach (actV ST77) 6 GW77 x := by
  obtain ⟨h1, h2, h3⟩ := treeOK_sound ts77_chk
  have hl : T77S.length = 2047 := Nat.eq_of_beq_eq_true (by quickRfl)
  exact ⟨h1, by rw [h2, hl], h3⟩

theorem tu77_chk : treeOK (actM UM77) 4 4 (idF 24) T77U = true := by quickRfl

theorem tu77 : (treePts (actM UM77) 4 (idF 24) T77U).1.Nodup ∧
    (treePts (actM UM77) 4 (idF 24) T77U).1.length = 16 ∧
    ∀ x ∈ (treePts (actM UM77) 4 (idF 24) T77U).1, Reach (actM UM77) 4 (idF 24) x := by
  obtain ⟨h1, h2, h3⟩ := treeOK_sound tu77_chk
  have hl : T77U.length = 15 := Nat.eq_of_beq_eq_true (by quickRfl)
  exact ⟨h1, by rw [h2, hl], h3⟩

end CertificateChecks.KernelCo1M

end

module

public import Certificates.Kernel.Co1M.Base10077
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KC.TreeK

theorem tx77_chk : treeOK (actX H77 H77i) 2 11 TP77 T77X = true := by quickRfl

theorem tx77 : (treePts (actX H77 H77i) 2 TP77 T77X).1.Nodup ∧
    (treePts (actX H77 H77i) 2 TP77 T77X).1.length = 1386 ∧
    ∀ x ∈ (treePts (actX H77 H77i) 2 TP77 T77X).1, Reach (actX H77 H77i) 2 TP77 x := by
  obtain ⟨h1, h2, h3⟩ := treeOK_sound tx77_chk
  have hl : T77X.length = 1385 := Nat.eq_of_beq_eq_true (by quickRfl)
  exact ⟨h1, by rw [h2, hl], h3⟩

theorem tp77_chk : treeOK (actP G77) 3 5 1 T77P = true := by quickRfl

theorem tp77 : (treePts (actP G77) 3 1 T77P).1.Nodup ∧ (treePts (actP G77) 3 1 T77P).1.length = 23 ∧
    ∀ x ∈ (treePts (actP G77) 3 1 T77P).1, Reach (actP G77) 3 1 x := by
  obtain ⟨h1, h2, h3⟩ := treeOK_sound tp77_chk
  have hl : T77P.length = 22 := Nat.eq_of_beq_eq_true (by quickRfl)
  exact ⟨h1, by rw [h2, hl], h3⟩

theorem tp77_pts : (treePts (actP G77) 3 1 T77P).1.all (fun x => Nat.blt 0 x && Nat.blt x 24) = true := by
  quickRfl

end CertificateChecks.KernelCo1M

end

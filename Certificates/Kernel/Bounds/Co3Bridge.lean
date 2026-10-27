module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Bounds.Co3
import CFSG.Certificates.Kernel.CosetBounds
import CFSG.Certificates.Kernel.Bounds.Co3Alt.Binding
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelBounds

open CFSG.Certificates TauCeti

open CFSG.KBRoute.Co3Alt in
theorem co3 : Finite SporadicName.Co3.Group ∧
    Nat.card SporadicName.Co3.Group ≤ 495766656000 := by
  obtain ⟨h1, h2, h3, htop, l1, l2⟩ := Co3.facts_holds
  have hrels := KB.sword_rels _ rels_eq
  delta T1.ok at h1
  delta T2.ok at h2
  delta T3.ok at h3
  have s1 := KB.tableOk_sound _ hrels h1
  have s2 := KB.tableOk_sound _ hrels h2
  have s3 := KB.tableOk_sound _ hrels h3
  rw [KB.linkOk_sound _ (KB.tableOk_lens h1).2 l1] at s1
  rw [KB.linkOk_sound _ (KB.tableOk_lens h2).2 l2] at s2
  rw [show T3.words = [] from rfl, KB.wordSub_nil] at s3
  have c := KB.card_le_step s1 <| KB.card_le_step s2 <| KB.card_le_step s3 KB.card_bot_le
  exact (KB.finite_card_le_of_route _ gens_eq (by norm_num) htop c).imp id
    fun h => h.trans (Nat.le_of_ble_eq_true rfl)

end CertificateChecks.KernelBounds

end

module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Bounds.Fi23
import CFSG.Certificates.Kernel.CosetBounds
import CFSG.Certificates.Kernel.Bounds.Fi23Alt.Binding
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelBounds

open CFSG.Certificates TauCeti

open CFSG.KBRoute.Fi23Alt in
theorem fi23 : Finite SporadicName.Fi23.Group ∧
    Nat.card SporadicName.Fi23.Group ≤ 4089470473293004800 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, htop, l1, l2, l3, l4, l5, l6, l7⟩ :=
    Fi23.facts_holds
  have hrels := KB.sword_rels _ rels_eq
  delta T1.ok at h1
  delta T2.ok at h2
  delta T3.ok at h3
  delta T4.ok at h4
  delta T5.ok at h5
  delta T6.ok at h6
  delta T7.ok at h7
  delta T8.ok at h8
  have s1 := KB.tableOk_sound _ hrels h1
  have s2 := KB.tableOk_sound _ hrels h2
  have s3 := KB.tableOk_sound _ hrels h3
  have s4 := KB.tableOk_sound _ hrels h4
  have s5 := KB.tableOk_sound _ hrels h5
  have s6 := KB.tableOk_sound _ hrels h6
  have s7 := KB.tableOk_sound _ hrels h7
  have s8 := KB.tableOk_sound _ hrels h8
  rw [KB.linkOk_sound _ (KB.tableOk_lens h1).2 l1] at s1
  rw [KB.linkOk_sound _ (KB.tableOk_lens h2).2 l2] at s2
  rw [KB.linkOk_sound _ (KB.tableOk_lens h3).2 l3] at s3
  rw [KB.linkOk_sound _ (KB.tableOk_lens h4).2 l4] at s4
  rw [KB.linkOk_sound _ (KB.tableOk_lens h5).2 l5] at s5
  rw [KB.linkOk_sound _ (KB.tableOk_lens h6).2 l6] at s6
  rw [KB.linkOk_sound _ (KB.tableOk_lens h7).2 l7] at s7
  rw [show T8.words = [] from rfl, KB.wordSub_nil] at s8
  have c := KB.card_le_step s1 <| KB.card_le_step s2 <| KB.card_le_step s3 <|
    KB.card_le_step s4 <| KB.card_le_step s5 <| KB.card_le_step s6 <| KB.card_le_step s7 <|
    KB.card_le_step s8 KB.card_bot_le
  exact (KB.finite_card_le_of_route _ gens_eq (by norm_num) htop c).imp id
    fun h => h.trans (Nat.le_of_ble_eq_true rfl)

end CertificateChecks.KernelBounds

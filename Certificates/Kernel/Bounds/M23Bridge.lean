module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Bounds.M23
import CFSG.Certificates.Kernel.CosetBounds
import CFSG.Certificates.Kernel.Bounds.M23.Binding
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelBounds

open CFSG.Certificates TauCeti

open CFSG.KBRoute.M23 in
theorem m23 : Finite SporadicName.M23.Group ∧
    Nat.card SporadicName.M23.Group ≤ 10200960 := by
  obtain ⟨h1, htop, hpow⟩ := M23.facts_holds
  have hrels := KB.sword_rels _ rels_eq
  delta T1.ok at h1
  have s1 := KB.tableOk_sound _ hrels h1
  obtain ⟨w, hw, hk, hlen⟩ := KB.powOk_sound _ hrels (KB.tableOk_lens h1).1
    (KB.tableOk_lens h1).2 (KB.tableOk_alphaOk h1) hpow
  have hw1 : T1.words = [[(0, true), (1, true)]] := rfl
  rw [hw1, List.cons.injEq] at hw
  obtain ⟨rfl, -⟩ := hw
  rw [hw1] at s1
  have c := KB.card_le_step s1
    (KB.card_wordSub_single_le _ hk (hlen (by simp [bottom])))
  exact (KB.finite_card_le_of_route _ gens_eq (by norm_num) htop c).imp id
    fun h => h.trans (Nat.le_of_ble_eq_true rfl)

end CertificateChecks.KernelBounds

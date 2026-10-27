module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.K
public import CFSG.LocalAnalysis.UniquenessCase.UC6Grp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem H_ne_top : m.H ≠ ⊤ := by
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ m.Z, z ≠ 1 := by
    by_contra h
    push Not at h
    exact m.Z_ne_bot (eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 (h z hz))
  intro htop
  apply centralizer_singleton_ne_top Dat.standing.simple Dat.standing.nonab hz1
  rw [eq_top_iff]
  intro x hx
  have : x ∈ m.H := by rw [htop]; exact mem_top x
  rw [H, mem_centralizer_iff] at this
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact this z hz

theorem E_le_H : m.E ≤ m.H := m.hZ.E_le_centralizer

theorem six15 (h67 : R6_7 Dat) :
    Nat.card ↥(pCoreOf 2 (m.H ⊓ m.M)) ≤ 2 ∧
      (Nat.card ↥(pCoreOf 2 (m.H ⊓ m.M)) = 2 → m.r = 3) := by
  by_cases hO : pCoreOf 2 (m.H ⊓ m.M) = ⊥
  · rw [hO, Subgroup.card_bot]
    exact ⟨by norm_num, fun h => absurd h (by norm_num)⟩
  · have hsub : Dat.sig ⊆ Dat.sig1 := m.hσ1
    obtain ⟨hr3, t, ht, hOt, -⟩ := h67 hsub m.r m.hr m.d.odd m.E (fun x hx => m.R_le_M (m.E_le_R hx)) m.d.E_el m.d.E_card
      m.d.E_gamma m.H m.E_le_H m.H_ne_top hO m.hZ.not_le
    have hOt' : pCoreOf 2 (m.H ⊓ m.M) = zpowers t := hOt
    have hcard : Nat.card ↥(pCoreOf 2 (m.H ⊓ m.M)) = 2 := by
      rw [hOt', Nat.card_zpowers, ht]
    exact ⟨hcard.le, fun _ => hr3⟩

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G

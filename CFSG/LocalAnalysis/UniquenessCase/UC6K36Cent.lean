module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

namespace Hyp36

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem normalizer_le_of_le_of_ne_bot {A : Subgroup G} (hAE : A ≤ E) (hA : A ≠ ⊥) :
    normalizer (A : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hp1 : 1 < p := h.prime.one_lt
  have hAel : IsElemAbelian p A := h.elem.mono hAE
  obtain ⟨j, hj⟩ := (h.isPGroup.to_le hAE).exists_card_eq
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hA (Subgroup.eq_bot_of_card_eq A (by simpa using hj))
  have hrank : 1 ≤ CFSG.Open.pRank p A :=
    (Nat.one_le_iff_ne_zero.2 hj0).trans (CFSG.SectionRank.le_pRank hp1 le_rfl hAel hj)
  exact (le_sSup (s := {N | ∃ Q : Subgroup G, Q ≤ E ∧ 1 ≤ CFSG.Open.pRank p Q ∧
      N = Subgroup.normalizer (Q : Set G)}) ⟨A, hAE, hrank, rfl⟩ : normalizer (A : Set G) ≤
        rankThreeGamma 1 p E).trans h.gamma

theorem centralizer_le_of_ne_one {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    centralizer ({e} : Set G) ≤ M := by
  have hfix : ∀ g' ∈ centralizer ({e} : Set G), ∀ y ∈ zpowers e, g' * y * g'⁻¹ = y := by
    intro g' hg' y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute g' e := Subgroup.mem_centralizer_singleton_iff.1 hg'
    rw [(hc.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
  refine le_trans (fun g hg => ?_) (h.normalizer_le_of_le_of_ne_bot (A := zpowers e)
    (Subgroup.zpowers_le.2 he) (by simpa using he1))
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hfix g hg y hy]
    exact hy
  · intro hy
    have h2 := hfix g⁻¹ (Subgroup.inv_mem _ hg) _ hy
    have h3 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    have h4 : g * y * g⁻¹ = y := h2.symm.trans h3
    rwa [h4] at hy

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK

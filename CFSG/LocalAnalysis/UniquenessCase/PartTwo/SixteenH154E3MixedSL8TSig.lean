module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8SA2A2B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_sl28T_sig_eq_three (D : Data G) (S : s16h_Std D) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (h7 : 7 ∉ D.sig) : D.sig = {3} := by
  have hsub := s16h_sl28_sa2b_sig_subset_three_seven D S h hs2 ht ht2 ht1 htr hW hcomp hthin hrow
    hbad
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · obtain ⟨p, hp⟩ := S.hx.sig_nonempty
    have hp' := hsub hp
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp'
    rcases hp' with hp3 | hp7
    · rw [hp3] at hp
      exact hp
    · exact (h7 (hp7 ▸ hp)).elim
  · intro q hq
    have hq' := hsub hq
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hq'
    rcases hq' with hq3 | hq7
    · exact hq3
    · exact (h7 (hq7 ▸ hq)).elim

theorem s16h_e3_sl28T_evenRank_eq_three (D : Data G) (S : s16h_Std D) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (h7 : 7 ∉ D.sig) : evenRank G = 3 := by
  refine le_antisymm ?_ D.standing.rank
  by_contra hle
  obtain ⟨p, hp⟩ := S.hx.sig_nonempty
  have h4 : 4 ≤ CFSG.Open.pRank p D.M := S.hx.four_le (not_le.1 hle) p hp
  have hsub := s16h_sl28_sa2b_sig_subset_three_seven D S h hs2 ht ht2 ht1 htr hW hcomp hthin hrow
    hbad
  have hp37 : p = 3 ∨ p = 7 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hsub hp
  rcases hp37 with hp3 | hp7
  · rw [hp3] at h4
    have h3 : CFSG.Open.pRank 3 D.M ≤ 3 :=
      s16h_sl28_sa2_pRank_three_le_three D S h hs2 ht ht2 ht1 htr hW hcomp hthin hrow hbad h7
    omega
  · exact h7 (hp7 ▸ hp)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

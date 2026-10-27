module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Cond
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_l3_three_ne_bot_dim_le_two_sig
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowL3 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hd2 : rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2) :
    D.sig = {3} := by
  have hV := h.hyp151.isElemAbelian
  have hcfg : s16h_H5Cfg (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) t :=
    ⟨s15_Infra_vtil_sq_eq_one ⊥ V hV, ht, ht2, ht1, htr, hW, hcomp, hthin⟩
  have hBB7 : s16h_BlockBound (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) 7 1 := by
    have h1 : s16h_BlockBound (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) 7 1 :=
      s16h_H5_row_L3_block_of_autSub_one (q := 7)
        (fun E hE hEab => s16h_H5_row_L3_three_seven_rank hcfg hL3 hZ hd2 E hE hEab)
    simpa only [lBar] using h1
  have h7 : 7 ∉ D.sig := by
    intro h7mem
    obtain ⟨E, hEM, hEab, hEX⟩ :=
      s16h_exists_Eb_of_blockBound_one_two D h hs2.le h7mem (S.hx.three_le 7 h7mem) hBB7
    have hlt := hbad 7 h7mem E hEM hEab
    omega
  have hsub : ∀ q ∈ D.sig, q = 3 ∨ q = 7 := by
    intro q hq
    rcases eq_or_ne q 3 with hq3 | hq3
    · exact Or.inl hq3
    rcases eq_or_ne q 7 with hq7 | hq7
    · exact Or.inr hq7
    exfalso
    have hpp := D.sig_prime q hq
    have hBB : s16h_BlockBound (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) q 1 := by
      have h1 : s16h_BlockBound (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) q 1 :=
        s16h_H5_row_L3_one hcfg (le_refl 3) hL3 hpp.1 hpp.2 (Or.inl ⟨hq3, hq7⟩)
      simpa only [lBar] using h1
    obtain ⟨E, hEM, hEab, hEX⟩ :=
      s16h_exists_Eb_of_blockBound_one_two D h hs2.le hq (S.hx.three_le q hq) hBB
    have hlt := hbad q hq E hEM hEab
    omega
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
  · obtain ⟨q, hq⟩ := S.hx.sig_nonempty
    rcases hsub q hq with hq3 | hq7
    · rwa [hq3] at hq
    · exact absurd (hq7 ▸ hq) h7
  · intro q hq
    rcases hsub q hq with hq3 | hq7
    · exact hq3
    · exact absurd (hq7 ▸ hq) h7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8SA2BA
public import CFSG.GroupTheory.ElemAbelianRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_sa2_pRank_three_le_three (D : Data G) (S : s16h_Std D) {V L : Subgroup G}
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
    (h7 : 7 ∉ D.sig) :
    CFSG.Open.pRank 3 D.M ≤ 3 := by
  have hV := h.hyp151.isElemAbelian
  have hsub : D.sig ⊆ {3, 7} :=
    s16h_sl28_sa2b_sig_subset_three_seven D S h hs2 ht ht2 ht1 htr hW hcomp hthin hrow hbad
  have h3mem : 3 ∈ D.sig := by
    obtain ⟨p, hp⟩ := S.hx.sig_nonempty
    have hp' := hsub hp
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp'
    rcases hp' with hp3 | hp7
    · rwa [hp3] at hp
    · exact absurd (hp7 ▸ hp) h7
  refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) ?_
  intro E hEM hEab
  have hEn : barSub ⊥ V hV E ≤
      normalizer (barSub ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) :=
    s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 (le_of_eq hs2)
      (by norm_num : Odd 3) hEM hEab
  have hc : s16h_H5Cfg (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) t :=
    ⟨s15_Infra_vtil_sq_eq_one ⊥ V hV, ht, ht2, ht1, htr, hW, hcomp, hthin⟩
  have hBB : s16h_BlockBound (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) 3 2 :=
    s16h_H5_row_SL2_eight hc hrow 3 Nat.prime_three (by norm_num)
  have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 hBB hEM hEab hEn
  have hbad3 : Nat.card ↥(E ⊓ preBarSub D.M ⊥ V hV
      (centSub (wTil ⊥ V hV L))) < 3 ^ 2 := hbad 3 h3mem E hEM hEab
  have hPab : IsElemAbelian 3 (E ⊓ preBarSub D.M ⊥ V hV
      (centSub (wTil ⊥ V hV L))) := hEab.mono inf_le_left
  have hcard3 : Nat.card ↥(E ⊓ preBarSub D.M ⊥ V hV
      (centSub (wTil ⊥ V hV L))) = 3 ^ CFSG.Open.pRank 3 (E ⊓ preBarSub D.M ⊥ V hV
      (centSub (wTil ⊥ V hV L))) :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hPab
  have hlt2 : CFSG.Open.pRank 3 (E ⊓ preBarSub D.M ⊥ V hV
      (centSub (wTil ⊥ V hV L))) < 2 := by
    rw [hcard3] at hbad3
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 3)).1 hbad3
  have hle1 : CFSG.Open.pRank 3 (E ⊓ preBarSub D.M ⊥ V hV
      (centSub (wTil ⊥ V hV L))) ≤ 1 := by omega
  have hcard3le : Nat.card ↥(E ⊓ preBarSub D.M ⊥ V hV
      (centSub (wTil ⊥ V hV L))) ≤ 3 := by
    rw [hcard3]
    calc 3 ^ CFSG.Open.pRank 3 (E ⊓ preBarSub D.M ⊥ V hV
          (centSub (wTil ⊥ V hV L))) ≤ 3 ^ 1 :=
          pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 3) hle1
      _ = 3 := by norm_num
  calc Nat.card ↥E ≤ 3 ^ 2 * Nat.card ↥(E ⊓ preBarSub D.M ⊥ V hV
          (centSub (wTil ⊥ V hV L))) := hcard
    _ ≤ 3 ^ 2 * 3 := Nat.mul_le_mul_left _ hcard3le
    _ = 3 ^ 3 := by norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

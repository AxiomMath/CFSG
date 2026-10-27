module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedQ5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_false_of_sl2_sl3 {X : Type} [Group X] {a : ℕ} (ha : a = 2 ∨ a = 3)
    (h2 : IsSLn X 2 a) (h3 : IsSLn X 3 1) : False := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h2
  obtain ⟨K', hF', hfin', hK', ⟨e'⟩⟩ := h3
  letI := hF
  letI := hfin
  letI := hF'
  letI := hfin'
  have h168 : Nat.card X = 168 := by
    rw [Nat.card_congr e'.toEquiv,
      CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two (K := K') (by simpa using hK')]
  have hq : Nat.card X = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two]
  rw [h168, hK] at hq
  rcases ha with rfl | rfl <;> norm_num at hq

theorem s16h_mixed_open_unique
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
    (hU2 : R8100U2 D) (h920L28 : s16h_e3_R920L28 D)
    (hbig : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∨
      s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3) :
    ∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M ⊥ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hc : s16h_H5Cfg (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) t :=
    ⟨s15_Infra_vtil_sq_eq_one ⊥ V hV, ht, ht2, ht1, htr, hW, hcomp, hthin⟩
  have hJ := hJP (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV) (lBar ⊥ V hV L)
  have hl3 : ∀ {a : ℕ}, (a = 2 ∨ a = 3) → s16h_H5RowSL2 (lBar ⊥ V hV L) (commSub ⊤ (lBar ⊥ V hV L))
      (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) a →
      2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) := by
    intro a ha hr
    rcases hbig with hZ4 | hsum
    · exact hZ4
    · exact (s16h_e3_false_of_sl2_sl3 ha hr.1 hsum.1).elim
  rcases hW.2.2 with h1 | h2 | h3 | h4
  · exact (s16h_H5_not_pgroup hc h1).elim
  · exact (s16h_H5_not_tensor hc h2).elim
  · obtain ⟨-, hsum, -⟩ := h3
    rcases s16h_H5_thin_sum hc hsum with hr | hr
    · exact s16h_mixed_l3_unique D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad hr hbig
    · exact (hZ (hJ.1 (Or.inl hr))).elim
  · obtain ⟨hirr, -, -, h135⟩ := h4
    rcases s16h_H5_thin_one hc h135 with hr | hr | hr | hr | hr | hr | hr
    · exact s16h_mixed_l3_unique D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad hr hbig
    · exact (hZ (hJ.1 (Or.inl hr))).elim
    · exact s16h_mixed_sl2_four_unique D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
        hr (hl3 (Or.inl rfl) hr)
    · exact s16h_mixed_sl2_eight_unique D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
        hr (hl3 (Or.inr rfl) hr) hU2 h920L28
    · exact (hZ (hJ.1 (Or.inr (Or.inl hr)))).elim
    · exact (hZ (hJ.1 (Or.inr (Or.inr (Or.inl hr))))).elim
    · exact (hZ (hJ.1 (Or.inr (Or.inr (Or.inr ⟨hr, hirr⟩))))).elim

private theorem s16h_mixed_bot_aux
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
    (hbig : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ∨
      s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hU2 : R8100U2 D) (h920L28 : s16h_e3_R920L28 D) :
    ∀ w ∈ wSub ⊥ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M ⊥ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨-, hc⟩ := s16h_H5_rows hJP (s15_Infra_vtil_sq_eq_one ⊥ V hV) ht ht2 ht1 htr hW hcomp
    hthin
  by_cases hgood : ∃ q ∈ D.sig, ∃ E : Subgroup G, E ≤ D.M ∧ IsElemAbelian q E ∧
      q ^ 2 ≤ Nat.card ↥(E ⊓ preBarSub D.M ⊥ V hV (centSub (wTil ⊥ V hV L)))
  · obtain ⟨q, hq, E, hEM, hEab, hbigE⟩ := hgood
    exact s16h_unique₁_of_mixed_of_Eb D S hσ h hs2 hq ⟨E, hEM, hEab, hbigE⟩ hc
  · have hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
        Nat.card ↥(E ⊓ preBarSub D.M ⊥ V hV (centSub (wTil ⊥ V hV L))) < q ^ 2 :=
      fun q hq E hEM hEab => not_le.1 fun hle => hgood ⟨q, hq, E, hEM, hEab, hle⟩
    exact s16h_mixed_open_unique D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hU2 h920L28 hbig

theorem s16h_mixed_struct
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar V₀ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar V₀ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hall : ∀ q ∈ D.sig, ¬ s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 1)
    (hU2 : R8100U2 D) (h920L28 : s16h_e3_R920L28 D) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  rcases eq_or_ne V₀ ⊥ with h0 | h0
  swap
  · exact absurd (s15_inf_fixV_wTil_eq_bot_of_ne_bot h.hyp151 h0) hZ
  subst h0
  by_cases hL3 : s16h_H5L3Sum (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3
  · exact s16h_mixed_bot_aux D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ (Or.inr hL3)
      hU2 h920L28
  by_cases hZ2 : Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤ 2
  · exact s16h_mixed_rank_one D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hZ2 hL3
  exact s16h_mixed_bot_aux D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
    (Or.inl (not_le.1 hZ2)) hU2 h920L28

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

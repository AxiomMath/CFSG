module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPOrthC
public import CFSG.RankThree.S4Free.StellmacherOffender

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_kernel_of_h5Block_of_h5Fix
    {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hLA : L ≤ A) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hU : commSub (⊤ : Subgroup W) L = ⊤)
    (hblock : s16h_H5Block A L) (hfix : s16h_H5Fix A L q) :
    S168e3Kernel A q := by
  have hcent : centSub (commSub (⊤ : Subgroup W) L) = ⊥ := by
    rw [hU, CFSG.RankThree.S4Free.Stell.centSub_top]
  have hcard_cent : ∀ E : Subgroup (MulAut W),
      Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L)) = 1 := by
    intro E
    rw [hcent, inf_bot_eq, Subgroup.card_bot]
  have hrank : CFSG.Open.pRank q A ≤ 2 := by
    refine CFSG.SectionRank.pRank_le hq.one_lt (H := A) (k := 2) ?_
    intro E hEA hEab
    have h := hblock q hq hq2 E (le_inf hEA (hEA.trans hAN)) hEab
    rwa [hcard_cent E, mul_one] at h
  refine ⟨hrank, ?_⟩
  intro x hx1 E hEA hErank
  obtain ⟨hcomm, hpow⟩ := CFSG.Quasithin.A36B.IsElemAbelianOfRank.comm_pow hErank
  have hEab : IsElemAbelian q E :=
    ⟨⟨⟨hcomm⟩⟩, fun y hy => by
      simpa using congrArg Subtype.val (hpow ⟨y, hy⟩)⟩
  have hEcard : Nat.card ↥E = q ^ 2 :=
    CFSG.Quasithin.A38.card_eq_of_isElemAbelianOfRank hq hErank
  have hcardineq :
      q ^ 2 * Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L)) ≤ Nat.card ↥E := by
    rw [hcard_cent E, hEcard, mul_one]
  have hxmem : x ∈ commSub (⊤ : Subgroup W) L := by
    rw [hU]
    exact Subgroup.mem_top x
  obtain ⟨g, hgL, b, hbE, hbcent, hfixb⟩ :=
    hfix E (le_inf hEA (hEA.trans hAN)) hEab hcardineq x hxmem hx1
  exact ⟨g, hLA hgL, b, hbE,
    fun hb1 => hbcent (by rw [hb1]; exact (centSub _).one_mem), hfixb⟩

theorem s168e3_false_of_omegaMinus_four_of_s_eq_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : s15 D.M V₀ V hV L = 1) {m : ℕ} (hm : m = 2 ∨ m = 3)
    (hrow : s16h_H5RowO4 (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) m) : False := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  obtain ⟨t, ht, ht2, ht1, htr, hW⟩ := c.conc
  have hc : s16h_H5Cfg A H t :=
    { elem := s15_Infra_vtil_sq_eq_one V₀ V hV
      mem := ht
      sq := ht2
      ne := ht1
      tr := htr
      conc := hW
      comp := hcomp
      thin := hthin }
  have hU : commSub (⊤ : Subgroup W) H = ⊤ := by
    simpa [wTil, H, W, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hHA : H ≤ A := by
    simpa [H, A, lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W)) := by
    intro a ha
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs ha)
  have hrow' : s16h_H5RowO4 H (commSub (⊤ : Subgroup W) H)
      (commSub (⊤ : Subgroup W) H ⊓ fixV H) m := by
    simpa [H, W] using hrow
  have hZ : commSub (⊤ : Subgroup W) H ⊓ fixV H = ⊥ :=
    s16jp_row_O4 hc.elem (L := H) (by omega) hrow'
  obtain ⟨p, hpσ⟩ := c.std.hx.sig_nonempty
  have hpprime : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hrank2 : 2 ≤ CFSG.Open.pRank p A := c.two_le_pRank_mbar hpσ
  have hnotone : ¬ s16h_BlockBound A H p 1 := by
    intro hone
    obtain ⟨E, hEA, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hpprime.one_lt A
    have hle := hone E (le_inf hEA (hEA.trans hAN)) hEab
    have hcent : centSub (commSub (⊤ : Subgroup W) H) = ⊥ := by
      rw [hU, CFSG.RankThree.S4Free.Stell.centSub_top]
    have hcard : Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) H)) = 1 := by
      rw [hcent, inf_bot_eq, Subgroup.card_bot]
    rw [hcard, pow_one, mul_one] at hle
    have hge : p ^ 2 ≤ Nat.card E := by
      rw [hEcard]
      exact Nat.pow_le_pow_right hpprime.pos hrank2
    have hlt : p < p ^ 2 := by
      simpa using Nat.pow_lt_pow_right hpprime.one_lt (by norm_num : 1 < 2)
    omega
  rcases hm with hm | hm
  ·
    subst m
    have hblock : s16h_H5Block A H := s16h_H5_row_O4_two hc hrow'
    have hp3 : p = 3 := by
      by_contra hp3
      exact hnotone (s16h_H5_row_O4_two_one hc hrow' hpprime hp2 hp3)
    subst p
    have hfix : s16h_H5Fix A H 3 := s16h_H5_row_O4_two_fix hc hrow' hZ
    exact s168e3_false_of_kernel c Nat.prime_three hpσ
      (s168e3_kernel_of_h5Block_of_h5Fix Nat.prime_three (by norm_num) hHA hAN hU hblock hfix)
  ·
    subst m
    have hblock : s16h_H5Block A H := s16h_H5_row_O4_three hc hrow'
    have hp37 : p = 3 ∨ p = 7 := by
      by_contra h
      rw [not_or] at h
      exact hnotone (s16h_H5_row_O4_three_one hc hrow' hpprime hp2 h.1 h.2)
    have hfix : s16h_H5Fix A H p := s16h_H5_row_O4_three_fix hc hrow' hZ hp37
    exact s168e3_false_of_kernel c hpprime hpσ
      (s168e3_kernel_of_h5Block_of_h5Fix hpprime hp2 hHA hAN hU hblock hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

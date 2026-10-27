module

public import CFSG.Monster.B.TwoA.Sp8.FlagStab
public import CFSG.Monster.B.TwoA.Sp8.P0Rank
public import Certificates.Certificate812463
public import CFSG.Monster.B.TwoA.Sp8.P0RankBase

set_option linter.unusedSectionVars false

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Open
open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank


@[expose] def nfD (g : ℕ × ℕ × ℕ) : Dfull := lD g.1 * tD g.2.1 * uE g.2.2

@[expose] def nfGrp (gs : List (ℕ × ℕ × ℕ)) : Subgroup Dfull :=
  Subgroup.closure {g | ∃ c ∈ gs, g = nfD c}

@[expose] def xD : Dfull := wordX xWord

@[expose] def yD : Dfull := wordX yWord

@[expose] def xT9inv : List ℕ := [1, 2, 4, 60, 16, 8, 65, 131, 256]

theorem wordX_nfWord (g : ℕ × ℕ × ℕ) : wordX (nfWord g) = nfD g := by
  simp only [nfWord, nfD, lD, tD, uE, wordX_append, mul_assoc]

private theorem isElemAbelian_nfGrp {gs : List (ℕ × ℕ × ℕ)}
    (hgs : gs ∈ [gensA1, gensA2, gensA4']) : IsElemAbelian 2 (nfGrp gs) := by
  have h := Certificates.certificate812463.1 gs hgs
  simp only [wordX_nfWord] at h
  exact h

theorem isElemAbelian_A1 : IsElemAbelian 2 (nfGrp gensA1) :=
  isElemAbelian_nfGrp List.mem_cons_self

theorem isElemAbelian_A2 : IsElemAbelian 2 (nfGrp gensA2) :=
  isElemAbelian_nfGrp (List.mem_cons_of_mem _ List.mem_cons_self)

theorem isElemAbelian_A4' : IsElemAbelian 2 (nfGrp gensA4') :=
  isElemAbelian_nfGrp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

private theorem tD_zero_eq_one : tD 0 = (1 : Dfull) := by
  have h : tD 0 * tD 0 = tD 0 := by rw [← tD_xor, Nat.xor_self]
  exact (mul_left_cancel (by rw [mul_one]; exact h.symm)).symm

private theorem lD_zero_eq_one : lD 0 = (1 : Dfull) := by
  rw [lD_eq_prod]
  simp

private theorem uProd_zero : uProd 0 = ([] : List XLetter) := by decide +kernel

private theorem uE_zero_eq_one : uE 0 = (1 : Dfull) := by
  rw [uE, uProd_zero, wordX_nil]

private theorem nfD_mem_P0 (c : ℕ × ℕ × ℕ) : nfD c ∈ P0 := by
  unfold nfD
  exact P0.mul_mem (P0.mul_mem (Lgrp_le_P0 (lD_mem_Lgrp c.1))
    (Lgrp_le_P0 (T9_le_Lgrp (tD_mem_T9 c.2.1)))) (uE_mem_P0 c.2.2)

private theorem nfD_mem_nfGrp {gs : List (ℕ × ℕ × ℕ)} {c : ℕ × ℕ × ℕ} (hc : c ∈ gs) :
    nfD c ∈ nfGrp gs := by
  unfold nfGrp
  exact Subgroup.subset_closure ⟨c, hc, rfl⟩

private theorem nfD_eq_lD_mul_tD {c : ℕ × ℕ × ℕ} (hκ : c.2.2 = 0) :
    nfD c = lD c.1 * tD c.2.1 := by
  unfold nfD
  rw [hκ, uE_zero_eq_one, mul_one]

private theorem nfD_eq_tD {c : ℕ × ℕ × ℕ} (h1 : c.1 = 0) (h2 : c.2.2 = 0) :
    nfD c = tD c.2.1 := by
  unfold nfD
  rw [h1, h2, lD_zero_eq_one, uE_zero_eq_one, one_mul, mul_one]

private theorem uCoord_nfD (c : ℕ × ℕ × ℕ) (hP0 : nfD c ∈ P0) :
    uCoord ⟨nfD c, hP0⟩ = Multiplicative.ofAdd (bvec 10 c.2.2) := by
  have hL : lD c.1 * tD c.2.1 ∈ Lgrp :=
    Lgrp.mul_mem (lD_mem_Lgrp c.1) (T9_le_Lgrp (tD_mem_T9 c.2.1))
  have hP0L : lD c.1 * tD c.2.1 ∈ P0 := Lgrp_le_P0 hL
  have hg : (⟨nfD c, hP0⟩ : P0) =
      ⟨lD c.1 * tD c.2.1, hP0L⟩ * ⟨uE c.2.2, uE_mem_P0 c.2.2⟩ := Subtype.ext rfl
  have h1 : uCoord ⟨lD c.1 * tD c.2.1, hP0L⟩ = 1 := (uCoord_eq_one_iff _).mpr hL
  rw [hg, map_mul, h1, uCoord_uE, one_mul]

private theorem xorSpan_induction {P : ℕ → Prop} (h0 : P 0)
    (hxor : ∀ a b, P a → P b → P (a ^^^ b)) :
    ∀ (l : List ℕ), (∀ a ∈ l, P a) → ∀ x ∈ xorSpan l, P x := by
  intro l
  induction l with
  | nil =>
    intro _ x hx
    rw [xorSpan, List.mem_singleton] at hx
    exact hx ▸ h0
  | cons a l ih =>
    intro hl x hx
    rw [xorSpan, List.mem_append, List.mem_map] at hx
    rcases hx with hx | ⟨b, hb, rfl⟩
    · exact ih (fun c hc => hl c (List.mem_cons_of_mem a hc)) x hx
    · exact hxor a b (hl a List.mem_cons_self)
        (ih (fun c hc => hl c (List.mem_cons_of_mem a hc)) b hb)

private theorem xorSpan_subset {S : Finset ℕ} (hS : XorClosed S) {l : List ℕ}
    (hl : ∀ a ∈ l, a ∈ S) : ∀ x ∈ xorSpan l, x ∈ S :=
  xorSpan_induction hS.1 (fun a b ha hb => hS.2 a ha b hb) l hl

private theorem xorClosed_layerY (E : Subgroup Dfull) : XorClosed (layerY E) := by
  classical
  constructor
  · simp only [layerY, Finset.mem_filter, Finset.mem_range]
    exact ⟨by norm_num, by rw [tD_zero_eq_one]; exact E.one_mem⟩
  · intro a ha b hb
    simp only [layerY, Finset.mem_filter, Finset.mem_range] at ha hb ⊢
    exact ⟨Nat.xor_lt_two_pow ha.1 hb.1, by rw [tD_xor]; exact E.mul_mem ha.2 hb.2⟩

private theorem mem_layerD_of_mem {gs : List (ℕ × ℕ × ℕ)} {c : ℕ × ℕ × ℕ} (hc : c ∈ gs)
    (hκ : c.2.2 = 0) (hσ : c.1 < 2 ^ 16) : c.1 ∈ layerD (nfGrp gs) := by
  classical
  have hmem : nfD c ∈ nfGrp gs := nfD_mem_nfGrp hc
  have hL' : lD c.1 * tD c.2.1 ∈ Lgrp :=
    Lgrp.mul_mem (lD_mem_Lgrp c.1) (T9_le_Lgrp (tD_mem_T9 c.2.1))
  have hL : nfD c ∈ Lgrp := (nfD_eq_lD_mul_tD hκ) ▸ hL'
  refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hσ, ⟨⟨nfD c, hL⟩, hmem, ?_⟩⟩
  have hx : (⟨nfD c, hL⟩ : Lgrp) = ⟨lD c.1 * tD c.2.1, hL'⟩ :=
    Subtype.ext (nfD_eq_lD_mul_tD hκ)
  rw [hx]
  exact sCoord_lD_mul hσ (tD_mem_T9 c.2.1) hL'

private theorem mem_layerW_of_mem {gs : List (ℕ × ℕ × ℕ)} {c : ℕ × ℕ × ℕ} (hc : c ∈ gs)
    (hκ : c.2.2 < 2 ^ 10) : c.2.2 ∈ layerW (nfGrp gs) := by
  classical
  have hP0 : nfD c ∈ P0 := nfD_mem_P0 c
  have hmem : nfD c ∈ nfGrp gs := nfD_mem_nfGrp hc
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hκ,
    ⟨⟨nfD c, hP0⟩, hmem, uCoord_nfD c hP0⟩⟩

private theorem mem_layerY_of_mem {gs : List (ℕ × ℕ × ℕ)} {c : ℕ × ℕ × ℕ} (hc : c ∈ gs)
    (h1 : c.1 = 0) (h2 : c.2.2 = 0) (hτ : c.2.1 < 2 ^ 9) :
    c.2.1 ∈ layerY (nfGrp gs) := by
  classical
  refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hτ, ?_⟩
  rw [← nfD_eq_tD h1 h2]
  exact nfD_mem_nfGrp hc

private theorem xorSpan_mem_layerD {gs : List (ℕ × ℕ × ℕ)} {l : List ℕ}
    (hb : ∀ c ∈ gs, c.1 < 2 ^ 16)
    (hgen : ∀ a ∈ l, ∃ c ∈ gs, c.2.2 = 0 ∧ c.1 = a) :
    (xorSpan l).toFinset ⊆ layerD (nfGrp gs) := by
  classical
  intro x hx
  refine xorSpan_subset (xorClosed_layerD _) ?_ x (List.mem_toFinset.1 hx)
  intro a ha
  obtain ⟨c, hc, hκ, rfl⟩ := hgen a ha
  exact mem_layerD_of_mem hc hκ (hb c hc)

private theorem xorSpan_mem_layerW {gs : List (ℕ × ℕ × ℕ)} {l : List ℕ}
    (hb : ∀ c ∈ gs, c.2.2 < 2 ^ 10)
    (hgen : ∀ a ∈ l, ∃ c ∈ gs, c.2.2 = a) :
    (xorSpan l).toFinset ⊆ layerW (nfGrp gs) := by
  classical
  intro x hx
  refine xorSpan_subset (xorClosed_layerW _) ?_ x (List.mem_toFinset.1 hx)
  intro a ha
  obtain ⟨c, hc, rfl⟩ := hgen a ha
  exact mem_layerW_of_mem hc (hb c hc)

private theorem xorSpan_mem_layerY {gs : List (ℕ × ℕ × ℕ)} {l : List ℕ}
    (hb : ∀ c ∈ gs, c.2.1 < 2 ^ 9)
    (hgen : ∀ a ∈ l, ∃ c ∈ gs, c.1 = 0 ∧ c.2.2 = 0 ∧ c.2.1 = a) :
    (xorSpan l).toFinset ⊆ layerY (nfGrp gs) := by
  classical
  intro x hx
  refine xorSpan_subset (xorClosed_layerY _) ?_ x (List.mem_toFinset.1 hx)
  intro a ha
  obtain ⟨c, hc, h1, h2, rfl⟩ := hgen a ha
  exact mem_layerY_of_mem hc h1 h2 (hb c hc)

private theorem mem_xorSpan_of_lt {τ : ℕ} (hτ : τ < 2 ^ 9) :
    τ ∈ xorSpan [1, 2, 4, 8, 16, 32, 64, 128, 256] := by
  have h : ∀ x ∈ List.range (2 ^ 9), x ∈ xorSpan [1, 2, 4, 8, 16, 32, 64, 128, 256] := by
    decide +kernel
  exact h τ (List.mem_range.2 hτ)

private theorem two_pow_list :
    ([1, 2, 4, 8, 16, 32, 64, 128, 256] : List ℕ) = (List.range 9).map (fun k => 2 ^ k) := by
  decide +kernel

private theorem eq_left_of_mul_eq {a b c A B C : ℕ} (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C)
    (hb : 0 < b) (hc : 0 < c) (he : a * b * c = A * B * C) : a = A := by
  have hbc : 0 < b * c := Nat.mul_pos hb hc
  have he' : a * (b * c) = A * (B * C) := by rw [← mul_assoc, ← mul_assoc]; exact he
  by_contra hne
  have hlt : a < A := lt_of_le_of_ne h1 hne
  have h1' : a * (b * c) < A * (b * c) := Nat.mul_lt_mul_of_pos_right hlt hbc
  have h3' : A * (b * c) ≤ A * (B * C) := Nat.mul_le_mul_left A (Nat.mul_le_mul h2 h3)
  have h2' : a * (b * c) < A * (B * C) := h1'.trans_le h3'
  rw [← he'] at h2'
  exact absurd h2' (lt_irrefl _)

theorem nfGrp_le_P0 (gs : List (ℕ × ℕ × ℕ)) : nfGrp gs ≤ P0 := by
  unfold nfGrp
  rw [Subgroup.closure_le]
  rintro g ⟨c, -, rfl⟩
  exact nfD_mem_P0 c

private theorem lftD_mem_Xgrp (k : ℕ) :
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.lftD k ∈ Xgrp :=
  H1_le_Xgrp (CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.lftD_mem_H1 k)

theorem xD_mem_Xgrp : xD ∈ Xgrp := by
  have hx : xD = CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.lftD 27 *
      (CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.lftD 28 *
        CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.lftD 27) := by
    unfold xD xWord
    simp only [wordX_cons, wordX_nil, toD_lift, mul_one]
  rw [hx]
  exact Xgrp.mul_mem (lftD_mem_Xgrp 27) (Xgrp.mul_mem (lftD_mem_Xgrp 28) (lftD_mem_Xgrp 27))

theorem yD_mem_Xgrp : yD ∈ Xgrp := by
  have hy : yD = CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.lftD 30 := by
    unfold yD yWord
    simp only [wordX_cons, wordX_nil, toD_lift, mul_one]
  rw [hy]
  exact lftD_mem_Xgrp 30

theorem exists_tD_of_mem_T9 {t : Dfull} (ht : t ∈ T9) : ∃ τ < 2 ^ 9, t = tD τ := by
  have h : t ∈ Psi9Hom.range := by rw [range_Psi9Hom]; exact ht
  obtain ⟨v, hv⟩ := h
  obtain ⟨τ, hτ, hb⟩ := CFSG.KC.BvecLoop.exists_bvec 9 v.toAdd
  refine ⟨τ, hτ, ?_⟩
  rw [tD_eq, hb, ← hv]
  rfl

theorem xD_conj_tD {τ : ℕ} (hτ : τ < 2 ^ 9) : xD * tD τ * xD⁻¹ = tD (colsAct xT9 τ) :=
  Certificates.certificate812463.2.1 τ hτ

theorem xD_inv_conj_tD {τ : ℕ} (hτ : τ < 2 ^ 9) :
    xD⁻¹ * tD τ * xD = tD (colsAct xT9inv τ) := by
  have hlt : colsAct xT9inv τ < 2 ^ 9 := by
    have hb : ∀ c ∈ xT9inv, c < 2 ^ 9 := by decide +kernel
    exact colsAct_lt hb τ
  have hfix : colsAct xT9 (colsAct xT9inv τ) = τ := by
    have h : ∀ x ∈ List.range (2 ^ 9), colsAct xT9 (colsAct xT9inv x) = x := by decide +kernel
    exact h τ (List.mem_range.2 hτ)
  have h := xD_conj_tD hlt
  rw [hfix] at h
  rw [← h]
  group

theorem yD_conj_tD {τ : ℕ} (hτ : τ < 2 ^ 9) : yD * tD τ * yD⁻¹ = tD (colsAct yT9 τ) :=
  Certificates.certificate812463.2.2 τ hτ

theorem yD_inv_conj_tD {τ : ℕ} (hτ : τ < 2 ^ 9) :
    yD⁻¹ * tD τ * yD = tD (colsAct yT9 τ) := by
  have hlt : colsAct yT9 τ < 2 ^ 9 := by
    have hb : ∀ c ∈ yT9, c < 2 ^ 9 := by decide +kernel
    exact colsAct_lt hb τ
  have hfix : colsAct yT9 (colsAct yT9 τ) = τ := by
    have h : ∀ x ∈ List.range (2 ^ 9), colsAct yT9 (colsAct yT9 x) = x := by decide +kernel
    exact h τ (List.mem_range.2 hτ)
  have h := yD_conj_tD hlt
  rw [hfix] at h
  rw [← h]
  group

theorem nfD_conj_tD (c : ℕ × ℕ × ℕ) {τ : ℕ} (hτ : τ < 2 ^ 9) :
    nfD c * tD τ * (nfD c)⁻¹ = tD (actK p0Data.uConjT c.2.2 τ) := by
  have hP0 : nfD c ∈ P0 := nfD_mem_P0 c
  have hmem : nfD c * tD τ * (nfD c)⁻¹ ∈ T9 := conj_mem_T9 hP0 (tD_mem_T9 τ)
  refine eq_of_tVec_eq hmem (tD_mem_T9 _) ?_
  rw [tVec_conj ⟨nfD c, hP0⟩ (tD_mem_T9 τ), uCoord_nfD c hP0, toAdd_ofAdd, tVec_tD,
    ← bvec_actK_uConjT c.2.2 hτ, tVec_tD]

theorem layers_eq_of_le_P0 {E : Subgroup Dfull} (hE : E ≤ P0) (hEa : IsElemAbelian 2 E)
    {SD SW SY : Finset ℕ} (hD : SD ⊆ layerD E) (hW : SW ⊆ layerW E) (hY : SY ⊆ layerY E)
    (hc : SD.card * SW.card * SY.card = 2 ^ 14) :
    layerD E = SD ∧ layerW E = SW ∧ layerY E = SY ∧ Nat.card E = 2 ^ 14 := by
  have hcard := natCard_eq_layers hE
  have hle := card_le_of_le_P0 E hE hEa
  have haD : SD.card ≤ (layerD E).card := Finset.card_le_card hD
  have haW : SW.card ≤ (layerW E).card := Finset.card_le_card hW
  have haY : SY.card ≤ (layerY E).card := Finset.card_le_card hY
  have hprodle : SD.card * SW.card * SY.card ≤
      (layerD E).card * (layerW E).card * (layerY E).card :=
    Nat.mul_le_mul (Nat.mul_le_mul haD haW) haY
  have hup : (layerD E).card * (layerW E).card * (layerY E).card ≤ 2 ^ 14 := by
    rw [← hcard]
    exact hle
  have hEq : SD.card * SW.card * SY.card =
      (layerD E).card * (layerW E).card * (layerY E).card :=
    le_antisymm hprodle (by rw [hc]; exact hup)
  have hpos : 0 < SD.card * SW.card * SY.card := by rw [hc]; norm_num
  have hposY : 0 < SY.card := Nat.pos_of_mul_pos_left hpos
  have hposW : 0 < SW.card := Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right hpos)
  have hposD : 0 < SD.card := Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right hpos)
  have hSD : SD.card = (layerD E).card := eq_left_of_mul_eq haD haW haY hposW hposY hEq
  have hSW : SW.card = (layerW E).card := by
    refine eq_left_of_mul_eq (a := SW.card) (b := SY.card) (c := SD.card)
      (A := (layerW E).card) (B := (layerY E).card) (C := (layerD E).card)
      haW haY haD hposY hposD ?_
    calc SW.card * SY.card * SD.card = SD.card * SW.card * SY.card := by ring
      _ = (layerD E).card * (layerW E).card * (layerY E).card := hEq
      _ = (layerW E).card * (layerY E).card * (layerD E).card := by ring
  have hSY : SY.card = (layerY E).card := by
    refine eq_left_of_mul_eq (a := SY.card) (b := SD.card) (c := SW.card)
      (A := (layerY E).card) (B := (layerD E).card) (C := (layerW E).card)
      haY haD haW hposD hposW ?_
    calc SY.card * SD.card * SW.card = SD.card * SW.card * SY.card := by ring
      _ = (layerD E).card * (layerW E).card * (layerY E).card := hEq
      _ = (layerY E).card * (layerD E).card * (layerW E).card := by ring
  have hD' : layerD E = SD := (Finset.eq_of_subset_of_card_le hD (by rw [hSD])).symm
  have hW' : layerW E = SW := (Finset.eq_of_subset_of_card_le hW (by rw [hSW])).symm
  have hY' : layerY E = SY := (Finset.eq_of_subset_of_card_le hY (by rw [hSY])).symm
  have hcardE : Nat.card E = 2 ^ 14 := by
    rw [hcard, hD', hW', hY', hc]
  exact ⟨hD', hW', hY', hcardE⟩

theorem layers_A1 :
    layerD (nfGrp gensA1) = (xorSpan [14479, 52645, 64475, 52504, 43198]).toFinset ∧
      layerW (nfGrp gensA1) = {0} ∧ layerY (nfGrp gensA1) = Finset.range (2 ^ 9) ∧
      Nat.card (nfGrp gensA1) = 2 ^ 14 := by
  have hE : nfGrp gensA1 ≤ P0 := nfGrp_le_P0 gensA1
  have hEa : IsElemAbelian 2 (nfGrp gensA1) := isElemAbelian_A1
  have hbd : ∀ c ∈ gensA1, c.1 < 2 ^ 16 ∧ c.2.1 < 2 ^ 9 ∧ c.2.2 < 2 ^ 10 := by decide +kernel
  have hDsub : (xorSpan [14479, 52645, 64475, 52504, 43198]).toFinset ⊆
      layerD (nfGrp gensA1) :=
    xorSpan_mem_layerD (fun c hc => (hbd c hc).1) (by decide +kernel)
  have hWsub : ({0} : Finset ℕ) ⊆ layerW (nfGrp gensA1) := by
    intro x hx
    rw [Finset.mem_singleton.1 hx]
    exact (xorClosed_layerW _).1
  have hgenMem : ∀ k ∈ List.range 9, (0, 2 ^ k, 0) ∈ gensA1 := by decide +kernel
  have hpowlt : ∀ k ∈ List.range 9, 2 ^ k < 2 ^ 9 := by decide +kernel
  have hYgen : ∀ a ∈ [1, 2, 4, 8, 16, 32, 64, 128, 256], a ∈ layerY (nfGrp gensA1) := by
    intro a ha
    rw [two_pow_list] at ha
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
    exact mem_layerY_of_mem (hgenMem k hk) rfl rfl (hpowlt k hk)
  have hYsub : Finset.range (2 ^ 9) ⊆ layerY (nfGrp gensA1) := by
    intro x hx
    exact xorSpan_subset (xorClosed_layerY _) hYgen x
      (mem_xorSpan_of_lt (Finset.mem_range.1 hx))
  have hc1 : (xorSpan [14479, 52645, 64475, 52504, 43198]).toFinset.card = 32 := by
    decide +kernel
  have hc2 : ({0} : Finset ℕ).card = 1 := by simp
  have hc3 : (Finset.range (2 ^ 9)).card = 512 := by rw [Finset.card_range]; norm_num
  have hc : (xorSpan [14479, 52645, 64475, 52504, 43198]).toFinset.card *
      ({0} : Finset ℕ).card * (Finset.range (2 ^ 9)).card = 2 ^ 14 := by
    rw [hc1, hc2, hc3]
    norm_num
  exact layers_eq_of_le_P0 hE hEa hDsub hWsub hYsub hc

theorem layers_A2 :
    layerD (nfGrp gensA2) = (xorSpan [132, 12, 68, 4]).toFinset ∧
      layerW (nfGrp gensA2) = (xorSpan [268, 195, 8, 207, 11]).toFinset ∧
      layerY (nfGrp gensA2) = (xorSpan [2, 48, 304, 268, 271]).toFinset ∧
      Nat.card (nfGrp gensA2) = 2 ^ 14 := by
  have hE : nfGrp gensA2 ≤ P0 := nfGrp_le_P0 gensA2
  have hEa : IsElemAbelian 2 (nfGrp gensA2) := isElemAbelian_A2
  have hbd : ∀ c ∈ gensA2, c.1 < 2 ^ 16 ∧ c.2.1 < 2 ^ 9 ∧ c.2.2 < 2 ^ 10 := by decide +kernel
  have hDsub : (xorSpan [132, 12, 68, 4]).toFinset ⊆ layerD (nfGrp gensA2) :=
    xorSpan_mem_layerD (fun c hc => (hbd c hc).1) (by decide +kernel)
  have hWsub : (xorSpan [268, 195, 8, 207, 11]).toFinset ⊆ layerW (nfGrp gensA2) :=
    xorSpan_mem_layerW (fun c hc => (hbd c hc).2.2) (by decide +kernel)
  have hYsub : (xorSpan [2, 48, 304, 268, 271]).toFinset ⊆ layerY (nfGrp gensA2) :=
    xorSpan_mem_layerY (fun c hc => (hbd c hc).2.1) (by decide +kernel)
  have hc1 : (xorSpan [132, 12, 68, 4]).toFinset.card = 16 := by decide +kernel
  have hc2 : (xorSpan [268, 195, 8, 207, 11]).toFinset.card = 32 := by decide +kernel
  have hc3 : (xorSpan [2, 48, 304, 268, 271]).toFinset.card = 32 := by decide +kernel
  have hc : (xorSpan [132, 12, 68, 4]).toFinset.card *
      (xorSpan [268, 195, 8, 207, 11]).toFinset.card *
      (xorSpan [2, 48, 304, 268, 271]).toFinset.card = 2 ^ 14 := by
    rw [hc1, hc2, hc3]
    norm_num
  exact layers_eq_of_le_P0 hE hEa hDsub hWsub hYsub hc

theorem layers_A4' :
    layerD (nfGrp gensA4') = (xorSpan [132, 136, 68, 4]).toFinset ∧
      layerW (nfGrp gensA4') = (xorSpan [333, 325, 203, 389, 5]).toFinset ∧
      layerY (nfGrp gensA4') = (xorSpan [284, 48, 63, 288, 2]).toFinset ∧
      Nat.card (nfGrp gensA4') = 2 ^ 14 := by
  have hE : nfGrp gensA4' ≤ P0 := nfGrp_le_P0 gensA4'
  have hEa : IsElemAbelian 2 (nfGrp gensA4') := isElemAbelian_A4'
  have hbd : ∀ c ∈ gensA4', c.1 < 2 ^ 16 ∧ c.2.1 < 2 ^ 9 ∧ c.2.2 < 2 ^ 10 := by decide +kernel
  have hDsub : (xorSpan [132, 136, 68, 4]).toFinset ⊆ layerD (nfGrp gensA4') :=
    xorSpan_mem_layerD (fun c hc => (hbd c hc).1) (by decide +kernel)
  have hWsub : (xorSpan [333, 325, 203, 389, 5]).toFinset ⊆ layerW (nfGrp gensA4') :=
    xorSpan_mem_layerW (fun c hc => (hbd c hc).2.2) (by decide +kernel)
  have hYsub : (xorSpan [284, 48, 63, 288, 2]).toFinset ⊆ layerY (nfGrp gensA4') :=
    xorSpan_mem_layerY (fun c hc => (hbd c hc).2.1) (by decide +kernel)
  have hc1 : (xorSpan [132, 136, 68, 4]).toFinset.card = 16 := by decide +kernel
  have hc2 : (xorSpan [333, 325, 203, 389, 5]).toFinset.card = 32 := by decide +kernel
  have hc3 : (xorSpan [284, 48, 63, 288, 2]).toFinset.card = 32 := by decide +kernel
  have hc : (xorSpan [132, 136, 68, 4]).toFinset.card *
      (xorSpan [333, 325, 203, 389, 5]).toFinset.card *
      (xorSpan [284, 48, 63, 288, 2]).toFinset.card = 2 ^ 14 := by
    rw [hc1, hc2, hc3]
    norm_num
  exact layers_eq_of_le_P0 hE hEa hDsub hWsub hYsub hc

end CFSG.Monster.B.TwoA.Sp8.WordRel

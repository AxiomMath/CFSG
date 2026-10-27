module

public import CFSG.Monster.B.TwoA.Sp8.P0LCoord
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import Certificates.Certificate812461Base

set_option linter.unusedSectionVars false

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix
open scoped commutatorElement


@[expose] def P0 : Subgroup Dfull := PLam lam0

theorem Lgrp_le_P0 : Lgrp ≤ P0 := by
  simpa only [P0] using Lgrp_le_PLam lam0

theorem natCard_P0 : Nat.card P0 = 2 ^ 35 := by
  simpa only [P0] using natCard_PLam lam0_isotropic finrank_lam0

theorem conj_mem_Lgrp {g : Dfull} (hg : g ∈ P0) {x : Dfull} (hx : x ∈ Lgrp) :
    g * x * g⁻¹ ∈ Lgrp := by
  have hgX : g ∈ Xgrp := (Subgroup.mem_inf.1 (show g ∈ PLam lam0 from hg)).1
  rw [Lgrp] at hx ⊢
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro a ha
  have hginv : g⁻¹ ∈ Subgroup.normalizer (A8 : Set Dfull) :=
    Subgroup.inv_mem _ (Xgrp_le_normalizer hgX)
  have hga : g⁻¹ * a * g ∈ A8 := by
    simpa using (Subgroup.mem_normalizer_iff.1 hginv a).1 ha
  have hx' := hx (g⁻¹ * a * g) hga
  calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [hx']
    _ = (g * x * g⁻¹) * a := by group

theorem conj_mem_T9 {g : Dfull} (hg : g ∈ P0) {t : Dfull} (ht : t ∈ T9) :
    g * t * g⁻¹ ∈ T9 := by
  have hgX : g ∈ Xgrp := (Subgroup.mem_inf.1 (show g ∈ PLam lam0 from hg)).1
  exact (Subgroup.mem_normalizer_iff.1 (Xgrp_le_normalizer_T9 hgX) t).1 ht

@[expose] def uE (κ : ℕ) : Dfull := wordX (uProd κ)

private theorem wordX_flatMap_uWord (κ : ℕ) (l : List ℕ) :
    wordX (l.flatMap fun k => if κ.testBit k then uWord k else []) =
      (l.map fun k => if κ.testBit k then uD k else 1).prod := by
  induction l with
  | nil => simp [wordX_nil]
  | cons a l ih =>
    rw [List.flatMap_cons, wordX_append, ih, List.map_cons, List.prod_cons]
    by_cases h : κ.testBit a
    · simp [h, uD]
    · simp [h, wordX_nil]

private theorem uE_eq_prod (κ : ℕ) :
    uE κ = ((List.range 10).map fun k => if κ.testBit k then uD k else 1).prod := by
  rw [uE, uProd]
  exact wordX_flatMap_uWord κ (List.range 10)

theorem uE_mem_P0 (κ : ℕ) : uE κ ∈ P0 := by
  
  rw [uE_eq_prod]
  refine Subgroup.list_prod_mem (K := P0) fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [List.mem_range] at hk
  by_cases h : κ.testBit k
  · rw [if_pos h]
    simpa only [P0] using uD_mem_PLam hk
  · rw [if_neg h]
    exact Subgroup.one_mem _

@[expose] def bMap (k : ℕ) (v : Fin 9 → ZMod 2) : Fin 9 → ZMod 2 :=
  ∑ j : Fin 9, v j • bvec 9 ((uConjTN.getD k []).getD j 0)

@[expose] def aMap (k : ℕ) (v : Fin 16 → ZMod 2) : Fin 16 → ZMod 2 :=
  ∑ j : Fin 16, v j • bvec 16 ((uConjLN.getD k []).getD j (0, 0)).1

@[expose] def bAct (κ : Fin 10 → ZMod 2) (v : Fin 9 → ZMod 2) : Fin 9 → ZMod 2 :=
  (List.finRange 10).foldr (fun k w => if κ k = 1 then bMap k w else w) v

@[expose] def aAct (κ : Fin 10 → ZMod 2) (v : Fin 16 → ZMod 2) : Fin 16 → ZMod 2 :=
  (List.finRange 10).foldr (fun k w => if κ k = 1 then aMap k w else w) v


private def bMask (n k a : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => if a.testBit n then bMask n k a ^^^ (uConjTN.getD k []).getD n 0 else bMask n k a

private def bActN (κ τ : ℕ) : ℕ :=
  (List.finRange 10).foldr
    (fun (k : Fin 10) t => if (bvec 10 κ) k = 1 then bMask 9 (k : ℕ) t else t) τ

private theorem sum_range_bvec (n k a : ℕ) :
    (∑ j ∈ Finset.range n, (if a.testBit j then (1 : ZMod 2) else 0) •
      bvec 9 ((uConjTN.getD k []).getD j 0)) = bvec 9 (bMask n k a) := by
  induction n with
  | zero => simp [bMask, bvec_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show bMask (n + 1) k a = if a.testBit n then
      bMask n k a ^^^ (uConjTN.getD k []).getD n 0 else bMask n k a from rfl]
    by_cases h : a.testBit n
    · rw [if_pos h, if_pos h, one_smul, bvec_xor]
    · rw [if_neg h, if_neg h, zero_smul, add_zero]

private theorem bMap_bvec (k a : ℕ) : bMap k (bvec 9 a) = bvec 9 (bMask 9 k a) := by
  rw [bMap]
  let f : ℕ → Fin 9 → ZMod 2 := fun j =>
    if h : j < 9 then (bvec 9 a ⟨j, h⟩) • bvec 9 ((uConjTN.getD k []).getD j 0) else 0
  calc (∑ i : Fin 9, (bvec 9 a i) • bvec 9 ((uConjTN.getD k []).getD (i : ℕ) 0))
      = ∑ i : Fin 9, f (i : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show f (i : ℕ) = (bvec 9 a ⟨(i : ℕ), by omega⟩) •
            bvec 9 ((uConjTN.getD k []).getD (i : ℕ) 0) from by
          simp only [f, dif_pos (by omega : (i : ℕ) < 9)]]
    _ = ∑ j ∈ Finset.range 9, f j := Fin.sum_univ_eq_sum_range f 9
    _ = ∑ j ∈ Finset.range 9, (if a.testBit j then (1 : ZMod 2) else 0) •
          bvec 9 ((uConjTN.getD k []).getD j 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show f j = (bvec 9 a ⟨j, Finset.mem_range.1 hj⟩) •
            bvec 9 ((uConjTN.getD k []).getD j 0) from by
          simp only [f, dif_pos (Finset.mem_range.1 hj)]]
        rw [bvec_apply]
    _ = bvec 9 (bMask 9 k a) := sum_range_bvec 9 k a

private theorem foldr_bvec (l : List (Fin 10)) (κ τ : ℕ) :
    l.foldr (fun (k : Fin 10) v =>
        if (bvec 10 κ) k = 1 then bMap (k : ℕ) v else v) (bvec 9 τ)
      = bvec 9 (l.foldr (fun (k : Fin 10) t =>
        if (bvec 10 κ) k = 1 then bMask 9 (k : ℕ) t else t) τ) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons]
    by_cases h : (bvec 10 κ) a = 1
    · rw [if_pos h, if_pos h, ih, bMap_bvec]
    · rw [if_neg h, if_neg h, ih]

private theorem bAct_bvec (κ τ : ℕ) :
    bAct (bvec 10 κ) (bvec 9 τ) = bvec 9 (bActN κ τ) := by
  simpa only [bAct, bActN] using foldr_bvec (List.finRange 10) κ τ

private theorem bActN_fixed_inj :
    ∀ κ < 1024, (∀ j < 9, bvec 9 (bActN κ (2 ^ j)) = bvec 9 (2 ^ j)) → κ = 0 := by
  decide +kernel




private theorem uD_mem_P0 {k : ℕ} (hk : k < 10) : uD k ∈ P0 := by
  simpa only [P0] using uD_mem_PLam hk

private theorem tVec_one : tVec 1 = 0 := by
  have h : tVec (1 * 1) = tVec 1 + tVec 1 := tVec_mul (T9.one_mem) (T9.one_mem)
  rw [one_mul] at h
  exact add_left_cancel (h.symm.trans (add_zero (tVec 1)).symm)

private theorem Psi9_zero : Psi9 (0 : Fin 9 → ZMod 2) = 1 := by
  rw [Psi9, show initV (0 : Fin 9 → ZMod 2) = 0 from rfl, Psi_zero']
  simp

private theorem tVec_Psi9 (v : Fin 9 → ZMod 2) : tVec (Psi9 v) = v := by
  rw [tVec, dif_pos (Psi9_mem_T9 v)]
  have h : tEquiv (Multiplicative.ofAdd v) = ⟨Psi9 v, Psi9_mem_T9 v⟩ :=
    Subtype.ext (coe_tEquiv _)
  calc (tEquiv.symm ⟨Psi9 v, Psi9_mem_T9 v⟩).toAdd
      = (Multiplicative.ofAdd v).toAdd := by rw [← h, tEquiv.symm_apply_apply]
    _ = v := rfl

private theorem bvec_two_pow (n : ℕ) (j : Fin n) :
    bvec n (2 ^ (j : ℕ)) = Pi.single j 1 := by
  funext i
  rw [bvec_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (j : ℕ) ≠ (i : ℕ) := fun e => h (Fin.ext e.symm)
    simp [h, h']

private theorem bMap_zero (k : ℕ) : bMap k 0 = 0 := by
  simp [bMap]

private theorem bMap_add (k : ℕ) (u v : Fin 9 → ZMod 2) :
    bMap k (u + v) = bMap k u + bMap k v := by
  simp only [bMap, Pi.add_apply, add_smul, Finset.sum_add_distrib]

private theorem tVec_tT (j : Fin 9) : tVec (tT j) = bvec 9 (2 ^ (j : ℕ)) := by
  rw [← tD_two_pow j, tVec_tD]

private theorem bMap_basis (k : ℕ) (j : Fin 9) :
    bMap k (bvec 9 (2 ^ (j : ℕ))) = bvec 9 ((uConjTN.getD k []).getD (j : ℕ) 0) := by
  rw [bMap, Finset.sum_eq_single j]
  · rw [bvec_apply, Nat.testBit_two_pow]
    simp
  · intro i _ hij
    rw [bvec_apply, Nat.testBit_two_pow]
    have h : (j : ℕ) ≠ (i : ℕ) := fun e => hij (Fin.ext e.symm)
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem tVec_conj_uD_basis (k : ℕ) (hk : k < 10) (j : Fin 9) :
    tVec (uD k * tT j * (uD k)⁻¹) = bMap k (tVec (tT j)) := by
  rw [tVec_tT]
  have hrel := uD_mul_tD (k := k) (j := (j : ℕ)) hk j.2
  rw [← tD_two_pow j]
  rw [show uD k * tD (2 ^ (j : ℕ)) * (uD k)⁻¹ =
      tD ((uConjTN.getD k []).getD (j : ℕ) 0) from by
    rw [hrel, mul_assoc, mul_inv_cancel, mul_one]]
  rw [tVec_tD, bMap_basis]

private def conjPhi (k : ℕ) (hk : k < 10) : (Fin 9 → ZMod 2) →+ (Fin 9 → ZMod 2) where
  toFun v := tVec (uD k * Psi9 v * (uD k)⁻¹)
  map_zero' := by
    rw [Psi9_zero, mul_one, mul_inv_cancel, tVec_one]
  map_add' := by
    intro v w
    rw [Psi9_add]
    have h1 : uD k * (Psi9 v * Psi9 w) * (uD k)⁻¹ =
        (uD k * Psi9 v * (uD k)⁻¹) * (uD k * Psi9 w * (uD k)⁻¹) := by group
    rw [h1, tVec_mul (conj_mem_T9 (uD_mem_P0 hk) (Psi9_mem_T9 v))
      (conj_mem_T9 (uD_mem_P0 hk) (Psi9_mem_T9 w))]

private def bMapHom (k : ℕ) : (Fin 9 → ZMod 2) →+ (Fin 9 → ZMod 2) where
  toFun := bMap k
  map_zero' := bMap_zero k
  map_add' := bMap_add k

private theorem conjPhi_single (k : ℕ) (hk : k < 10) (j : Fin 9) :
    conjPhi k hk (Pi.single j 1) = bMapHom k (Pi.single j 1) := by
  change tVec (uD k * Psi9 (Pi.single j 1) * (uD k)⁻¹) = bMap k (Pi.single j 1)
  rw [Psi9_single]
  rw [show Pi.single j (1 : ZMod 2) = bvec 9 (2 ^ (j : ℕ)) from (bvec_two_pow 9 j).symm]
  rw [← tVec_tT]
  exact tVec_conj_uD_basis k hk j

private theorem conjPhi_eq_bMapHom (k : ℕ) (hk : k < 10) :
    conjPhi k hk = bMapHom k := by
  apply AddMonoidHom.ext
  intro v
  have hv : v = ∑ j : Fin 9, Pi.single j (v j) := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne (Ne.symm hji)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  calc conjPhi k hk v
      = conjPhi k hk (∑ j : Fin 9, Pi.single j (v j)) := by
        conv_lhs => rw [hv]
    _ = ∑ j : Fin 9, conjPhi k hk (Pi.single j (v j)) := map_sum _ _ _
    _ = ∑ j : Fin 9, bMapHom k (Pi.single j (v j)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : v j = 0
        · rw [h, Pi.single_zero]
          simp
        · have h1 : v j = 1 := by
            rcases zmod2_cases (v j) with h0 | h1
            · exact absurd h0 h
            · exact h1
          rw [h1, conjPhi_single]
    _ = bMapHom k (∑ j : Fin 9, Pi.single j (v j)) := (map_sum _ _ _).symm
    _ = bMapHom k v := by
        conv_rhs => rw [hv]

private theorem tVec_conj_uD (k : ℕ) (hk : k < 10) {t : Dfull} (ht : t ∈ T9) :
    tVec (uD k * t * (uD k)⁻¹) = bMap k (tVec t) := by
  have ht_eq : t = Psi9 (tVec t) :=
    (eq_of_tVec_eq (Psi9_mem_T9 (tVec t)) ht (tVec_Psi9 (tVec t))).symm
  rw [ht_eq, tVec_Psi9]
  exact DFunLike.congr_fun (conjPhi_eq_bMapHom k hk) (tVec t)





private def uEl (l : List ℕ) (κ : ℕ) : Dfull :=
  wordX (l.flatMap fun k => if κ.testBit k then uWord k else [])

private theorem uEl_cons (a : ℕ) (l : List ℕ) (κ : ℕ) :
    uEl (a :: l) κ = (if κ.testBit a then uD a else 1) * uEl l κ := by
  rw [uEl, uEl, List.flatMap_cons, wordX_append]
  by_cases h : κ.testBit a
  · simp [h, uD]
  · simp [h, wordX_nil]

private theorem uEl_mem_P0 {l : List ℕ} (hl : ∀ k ∈ l, k < 10) (κ : ℕ) :
    uEl l κ ∈ P0 := by
  rw [uEl, wordX_flatMap_uWord]
  refine Subgroup.list_prod_mem (K := P0) fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  by_cases h : κ.testBit k
  · rw [if_pos h]
    simpa only [P0] using uD_mem_PLam (hl k hk)
  · rw [if_neg h]
    exact Subgroup.one_mem _

private theorem tVec_conj_uEl (l : List ℕ) (hl : ∀ k ∈ l, k < 10) (κ : ℕ)
    {t : Dfull} (ht : t ∈ T9) :
    tVec (uEl l κ * t * (uEl l κ)⁻¹) =
      l.foldr (fun k w => if κ.testBit k then bMap k w else w) (tVec t) := by
  induction l with
  | nil => simp [uEl, wordX_nil]
  | cons a l ih =>
    have hl' : ∀ k ∈ l, k < 10 := fun k hk => hl k (by simp [hk])
    have hmem : uEl l κ ∈ P0 := uEl_mem_P0 hl' κ
    have hy : uEl l κ * t * (uEl l κ)⁻¹ ∈ T9 := conj_mem_T9 hmem ht
    have hx : uEl (a :: l) κ * t * (uEl (a :: l) κ)⁻¹ =
        (if κ.testBit a then uD a else 1) * (uEl l κ * t * (uEl l κ)⁻¹) *
          (if κ.testBit a then uD a else 1)⁻¹ := by
      rw [uEl_cons]
      group
    rw [hx, List.foldr_cons]
    by_cases h : κ.testBit a
    · simp only [h, if_true]
      rw [tVec_conj_uD a (hl a (by simp)) hy, ih hl']
    · simpa [h] using ih hl' 

private theorem tVec_conj_uE (κ : ℕ) {t : Dfull} (ht : t ∈ T9) :
    tVec (uE κ * t * (uE κ)⁻¹) =
      (List.range 10).foldr (fun k w => if κ.testBit k then bMap k w else w) (tVec t) := by
  simpa only [uEl, uE, uProd] using
    tVec_conj_uEl (List.range 10) (fun k hk => List.mem_range.1 hk) κ ht

private theorem tT_mem_T9 (j : Fin 9) : tT j ∈ T9 := by
  rw [← tD_two_pow j]
  exact tD_mem_T9 _


private theorem T9_comm {a b : Dfull} (ha : a ∈ T9) (hb : b ∈ T9) : a * b = b * a := by
  apply eq_of_tVec_eq (T9.mul_mem ha hb) (T9.mul_mem hb ha)
  rw [tVec_mul ha hb, tVec_mul hb ha, add_comm]

private theorem foldr_range_finRange (n : ℕ) (hn : n ≤ 10) (κ : ℕ) (v : Fin 9 → ZMod 2) :
    (List.range n).foldr (fun k w => if κ.testBit k then bMap k w else w) v
      = (List.finRange n).foldr (fun (k : Fin n) w =>
        if (bvec 10 κ) ⟨(k : ℕ), by omega⟩ = 1 then bMap (k : ℕ) w else w) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.finRange_succ_last, List.foldr_append, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil, List.foldr_map, Fin.val_last,
      Fin.val_castSucc]
    have hbit : (bvec 10 κ) ⟨n, by omega⟩ = if κ.testBit n then 1 else 0 := by
      rw [bvec_apply]
    rw [show (if (bvec 10 κ) ⟨n, by omega⟩ = 1 then bMap n v else v) =
        (if κ.testBit n then bMap n v else v) from by
      rw [hbit]
      by_cases h : κ.testBit n <;> simp [h]]
    simpa only [Fin.coe_castSucc] using ih (by omega) (v := if κ.testBit n then bMap n v else v)

private theorem bAct_eq_range_fold (κ : ℕ) (v : Fin 9 → ZMod 2) :
    bAct (bvec 10 κ) v =
      (List.range 10).foldr (fun k w => if κ.testBit k then bMap k w else w) v := by
  rw [bAct]
  simpa only using (foldr_range_finRange 10 le_rfl κ v).symm

private theorem tVec_conj_uE_bAct (κ : ℕ) {t : Dfull} (ht : t ∈ T9) :
    tVec (uE κ * t * (uE κ)⁻¹) = bAct (bvec 10 κ) (tVec t) := by
  rw [tVec_conj_uE κ ht, bAct_eq_range_fold]

private theorem uE_mem_Lgrp_eq_zero {κ : ℕ} (hκ : κ < 1024) (hL : uE κ ∈ Lgrp) : κ = 0 := by
  have hcent := Lgrp_le_centralizer_T9 hL
  have hfix : ∀ j : Fin 9, bvec 9 (bActN κ (2 ^ (j : ℕ))) = bvec 9 (2 ^ (j : ℕ)) := by
    intro j
    have hcomm := Subgroup.mem_centralizer_iff.1 hcent (tT j) (tT_mem_T9 j)
    have hconj : uE κ * tT j * (uE κ)⁻¹ = tT j := by
      rw [← hcomm]
      group
    have h1 : tVec (uE κ * tT j * (uE κ)⁻¹) = tVec (tT j) := by rw [hconj]
    rw [tVec_conj_uE_bAct κ (tT_mem_T9 j), tVec_tT, bAct_bvec] at h1
    exact h1
  exact bActN_fixed_inj κ hκ (fun j hj => hfix ⟨j, hj⟩)

private abbrev Q := P0 ⧸ (Lgrp.subgroupOf P0)

private instance normal_Lgrp : (Lgrp.subgroupOf P0).Normal := ⟨by
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using conj_mem_Lgrp g.2 hn⟩


private def uBar (k : ℕ) : Q :=
  if h : k < 10 then QuotientGroup.mk' (Lgrp.subgroupOf P0) ⟨uD k, uD_mem_P0 h⟩ else 1

private theorem uBar_apply {k : ℕ} (hk : k < 10) :
    uBar k = QuotientGroup.mk' (Lgrp.subgroupOf P0) ⟨uD k, uD_mem_P0 hk⟩ := by
  simp [uBar, dif_pos hk]

private theorem uBar_comm_lt {j k : ℕ} (hj : j < 10) (hk : k < 10) :
    uBar j * uBar k = uBar k * uBar j := by
  rw [uBar_apply hj, uBar_apply hk, ← map_mul, ← map_mul]
  change ((⟨uD j, uD_mem_P0 hj⟩ * ⟨uD k, uD_mem_P0 hk⟩ : P0) : Q) =
    ((⟨uD k, uD_mem_P0 hk⟩ * ⟨uD j, uD_mem_P0 hj⟩ : P0) : Q)
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  have hrel := uD_mul_uD (j := j) (k := k) hj hk
  have hmem : lD ((uCommN.getD j []).getD k (0, 0)).1 *
      tD ((uCommN.getD j []).getD k (0, 0)).2 ∈ Lgrp :=
    Lgrp.mul_mem (lD_mem_Lgrp _) (T9_le_Lgrp (tD_mem_T9 _))
  convert hmem using 1
  rw [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_mul]
  change uD j * uD k / (uD k * uD j) =
    lD ((uCommN.getD j []).getD k (0, 0)).1 * tD ((uCommN.getD j []).getD k (0, 0)).2
  rw [hrel, div_eq_mul_inv]
  group

private theorem uBar_sq_lt {k : ℕ} (hk : k < 10) : uBar k * uBar k = 1 := by
  rw [uBar_apply hk, ← map_mul]
  change (((⟨uD k, uD_mem_P0 hk⟩ * ⟨uD k, uD_mem_P0 hk⟩ : P0)) : Q) = 1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hmem : lD (uSqN.getD k (0, 0)).1 * tD (uSqN.getD k (0, 0)).2 ∈ Lgrp :=
    Lgrp.mul_mem (lD_mem_Lgrp _) (T9_le_Lgrp (tD_mem_T9 _))
  convert hmem using 1
  change uD k * uD k = lD (uSqN.getD k (0, 0)).1 * tD (uSqN.getD k (0, 0)).2
  exact uD_mul_self hk

private theorem uBar_comm (j k : ℕ) : uBar j * uBar k = uBar k * uBar j := by
  by_cases hj : j < 10 <;> by_cases hk : k < 10
  · exact uBar_comm_lt hj hk
  · simp [uBar, hj, hk]
  · simp [uBar, hj, hk]
  · simp [uBar, hj, hk]

private theorem uBar_sq (k : ℕ) : uBar k * uBar k = 1 := by
  by_cases hk : k < 10
  · exact uBar_sq_lt hk
  · simp [uBar, hk]

private def uBarProd (κ : ℕ) : Q :=
  QuotientGroup.mk' (Lgrp.subgroupOf P0) ⟨uE κ, uE_mem_P0 κ⟩

private theorem natCard_Q : Nat.card Q = 1024 := by
  have hN : Nat.card (Lgrp.subgroupOf P0) = Nat.card Lgrp :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Lgrp_le_P0).toEquiv
  calc Nat.card Q = (Lgrp.subgroupOf P0).index :=
        (Subgroup.index_eq_card (H := Lgrp.subgroupOf P0)).symm
    _ = Nat.card P0 / Nat.card (Lgrp.subgroupOf P0) :=
        Subgroup.index_eq_card_div (H := Lgrp.subgroupOf P0)
    _ = 2 ^ 35 / 2 ^ 25 := by rw [natCard_P0, hN, natCard_Lgrp]
    _ = 1024 := by norm_num






private theorem comm_prod_map {M : Type*} [Monoid M] (b : Fin 10 → M)
    (hcomm : ∀ j k, b j * b k = b k * b j) (a : Fin 10) (l : List (Fin 10))
    (p : Fin 10 → ZMod 2) :
    b a * (l.map fun k => if p k = 1 then b k else 1).prod =
      (l.map fun k => if p k = 1 then b k else 1).prod * b a := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons]
    have hx : b a * (if p c = 1 then b c else 1) =
        (if p c = 1 then b c else 1) * b a := by
      by_cases h : p c = 1
      · simp [h, hcomm a c]
      · simp [h]
    calc b a * ((if p c = 1 then b c else 1) *
          (List.map (fun k => if p k = 1 then b k else 1) l).prod)
        = (b a * (if p c = 1 then b c else 1)) *
            (List.map (fun k => if p k = 1 then b k else 1) l).prod :=
          (mul_assoc _ _ _).symm
      _ = ((if p c = 1 then b c else 1) * b a) *
            (List.map (fun k => if p k = 1 then b k else 1) l).prod := by rw [hx]
      _ = (if p c = 1 then b c else 1) *
            (b a * (List.map (fun k => if p k = 1 then b k else 1) l).prod) :=
          mul_assoc _ _ _
      _ = (if p c = 1 then b c else 1) *
            ((List.map (fun k => if p k = 1 then b k else 1) l).prod * b a) := by rw [ih]
      _ = ((if p c = 1 then b c else 1) *
            (List.map (fun k => if p k = 1 then b k else 1) l).prod) * b a :=
          (mul_assoc _ _ _).symm

private theorem prod_add_eq {M : Type*} [Monoid M] (b : Fin 10 → M)
    (hcomm : ∀ j k, b j * b k = b k * b j) (hsq : ∀ k, b k * b k = 1)
    (l : List (Fin 10)) (v w : Fin 10 → ZMod 2) :
    (l.map fun k => if (v + w) k = 1 then b k else 1).prod =
      (l.map fun k => if v k = 1 then b k else 1).prod *
      (l.map fun k => if w k = 1 then b k else 1).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.prod_cons, ih, Pi.add_apply]
    set x : M := b a
    set P : M := (List.map (fun k => if v k = 1 then b k else 1) l).prod
    set Q : M := (List.map (fun k => if w k = 1 then b k else 1) l).prod
    have hcommP : x * P = P * x := comm_prod_map b hcomm a l v
    have hsqx : x * x = 1 := hsq a
    rcases zmod2_cases (v a) with hv | hv <;> rcases zmod2_cases (w a) with hw | hw <;>
      simp [hv, hw]
    · rw [← mul_assoc, hcommP, mul_assoc]
    · rw [mul_assoc]
    · calc P * Q = (x * x) * (P * Q) := by rw [hsqx, one_mul]
        _ = x * (x * (P * Q)) := mul_assoc _ _ _
        _ = x * ((x * P) * Q) := congrArg (fun z => x * z) (mul_assoc x P Q).symm
        _ = x * ((P * x) * Q) := congrArg (fun z => x * (z * Q)) hcommP
        _ = x * (P * (x * Q)) := congrArg (fun z => x * z) (mul_assoc P x Q)
        _ = (x * P) * (x * Q) := (mul_assoc _ _ _).symm

private theorem exists_bvec' (n : ℕ) (v : Fin n → ZMod 2) :
    ∃ a < 2 ^ n, bvec n a = v := by
  refine ⟨Nat.ofBits fun i => decide (v i = 1), Nat.ofBits_lt_two_pow _, ?_⟩
  funext i
  rw [bvec_apply, Nat.testBit_ofBits_lt _ _ i.2]
  rcases zmod2_cases (v i) with h | h <;> simp [h]

private theorem prod_finRange (n : ℕ) (f : ℕ → Q) :
    ((List.finRange n).map (fun k : Fin n => f k)).prod = ((List.range n).map f).prod := by
  have h : (List.finRange n).map (fun k : Fin n => f (k : ℕ)) =
      ((List.finRange n).map (fun k : Fin n => (k : ℕ))).map f := by
    rw [List.map_map]
    rfl
  change ((List.finRange n).map (fun k : Fin n => f (k : ℕ))).prod = _
  rw [h, List.map_coe_finRange_eq_range]

private theorem mk'_list_prod_eq (l : List ℕ) (hl : ∀ k ∈ l, k < 10) (κ : ℕ) :
    QuotientGroup.mk' (Lgrp.subgroupOf P0)
      ⟨(l.map fun k => if κ.testBit k then uD k else 1).prod,
        Subgroup.list_prod_mem (K := P0) (fun x hx => by
          rw [List.mem_map] at hx
          obtain ⟨k, hk, rfl⟩ := hx
          by_cases h : κ.testBit k
          · rw [if_pos h]; exact uD_mem_P0 (hl k hk)
          · rw [if_neg h]; exact Subgroup.one_mem _)⟩ =
      (l.map fun k => if κ.testBit k then uBar k else 1).prod := by
  let f : ℕ → P0 := fun k => if hk : k < 10 then
      if κ.testBit k then ⟨uD k, uD_mem_P0 hk⟩ else 1 else 1
  have hsub : (⟨(l.map fun k => if κ.testBit k then uD k else 1).prod,
      Subgroup.list_prod_mem (K := P0) (fun x hx => by
        rw [List.mem_map] at hx
        obtain ⟨k, hk, rfl⟩ := hx
        by_cases h : κ.testBit k
        · rw [if_pos h]; exact uD_mem_P0 (hl k hk)
        · rw [if_neg h]; exact Subgroup.one_mem _)⟩ : P0) = (l.map f).prod := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod]
    change (l.map (fun k => if κ.testBit k then uD k else 1)).prod =
      ((l.map f).map Subtype.val).prod
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hk10 := hl k hk
    by_cases h : κ.testBit k
    · simp [f, hk10, h]
    · simp [f, hk10, h]
  rw [hsub, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk10 := hl k hk
  by_cases h : κ.testBit k
  · simp [f, hk10, h, uBar_apply hk10]
  · simp [f, hk10, h]

private theorem uBarProd_eq_prod (κ : ℕ) :
    uBarProd κ = ((List.range 10).map fun k => if κ.testBit k then uBar k else 1).prod := by
  simpa only [uBarProd, uE_eq_prod] using
    mk'_list_prod_eq (List.range 10) (fun k hk => List.mem_range.1 hk) κ

private def psiFun (v : Fin 10 → ZMod 2) : Q :=
  ((List.finRange 10).map fun k => if v k = 1 then uBar k else 1).prod

private def psi : Multiplicative (Fin 10 → ZMod 2) →* Q where
  toFun v := psiFun v.toAdd
  map_one' := by
    simp [psiFun]
  map_mul' v w := by
    change ((List.finRange 10).map (fun k : Fin 10 =>
        if (v.toAdd + w.toAdd) k = 1 then uBar k else 1)).prod =
      ((List.finRange 10).map (fun k : Fin 10 =>
        if v.toAdd k = 1 then uBar k else 1)).prod *
      ((List.finRange 10).map (fun k : Fin 10 =>
        if w.toAdd k = 1 then uBar k else 1)).prod
    exact prod_add_eq (fun k : Fin 10 => uBar k)
      (fun j k => uBar_comm j k) (fun k => uBar_sq k) (List.finRange 10) v.toAdd w.toAdd

private theorem psi_bvec (κ : ℕ) :
    psi (Multiplicative.ofAdd (bvec 10 κ)) = uBarProd κ := by
  let gN : ℕ → Q := fun k => if hk : k < 10 then
    (if bvec 10 κ ⟨k, hk⟩ = 1 then uBar k else 1) else 1
  have hmap : (List.finRange 10).map (fun k : Fin 10 =>
      if bvec 10 κ k = 1 then uBar k else 1) =
      (List.finRange 10).map (fun k : Fin 10 => gN k) := by
    apply List.map_congr_left
    intro k hk
    simp [gN, k.isLt]
  change ((List.finRange 10).map (fun k : Fin 10 =>
      if bvec 10 κ k = 1 then uBar k else 1)).prod = uBarProd κ
  rw [hmap, prod_finRange, uBarProd_eq_prod]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk10 := List.mem_range.1 hk
  simp [gN, hk10, bvec_apply]

private theorem psi_inj : Function.Injective psi := by
  rw [injective_iff_map_eq_one]
  intro v hv
  obtain ⟨κ, hκ, hb⟩ := exists_bvec' 10 v.toAdd
  have hψ : psi v = psi (Multiplicative.ofAdd (bvec 10 κ)) := by
    rw [hb, ofAdd_toAdd]
  have hprod : uBarProd κ = 1 := by
    rw [← psi_bvec κ, ← hψ]
    exact hv
  have hmem : uE κ ∈ Lgrp := by
    have hq : QuotientGroup.mk' (Lgrp.subgroupOf P0) ⟨uE κ, uE_mem_P0 κ⟩ = 1 := hprod
    exact (Subgroup.mem_subgroupOf).mp ((QuotientGroup.eq_one_iff _).mp hq)
  have hκ0 := uE_mem_Lgrp_eq_zero hκ hmem
  apply Multiplicative.ext
  change v.toAdd = 0
  rw [← hb, hκ0, bvec_zero]

private theorem card_multiplicative_fin10 :
    Nat.card (Multiplicative (Fin 10 → ZMod 2)) = 1024 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_pi_const]
  norm_num [ZMod.card]

private theorem psi_bijective : Function.Bijective psi := by
  rw [@Nat.bijective_iff_injective_and_card _ _ 
    (Nat.finite_of_card_ne_zero (by rw [natCard_Q]; norm_num)) psi]
  exact ⟨psi_inj, by rw [card_multiplicative_fin10, natCard_Q]⟩

private noncomputable def psiEquiv : Multiplicative (Fin 10 → ZMod 2) ≃* Q :=
  MulEquiv.ofBijective psi psi_bijective

def uCoord : P0 →* Multiplicative (Fin 10 → ZMod 2) :=
  psiEquiv.symm.toMonoidHom.comp (QuotientGroup.mk' (Lgrp.subgroupOf P0))

theorem uCoord_uE (κ : ℕ) :
    uCoord ⟨uE κ, uE_mem_P0 κ⟩ = Multiplicative.ofAdd (bvec 10 κ) := by
  change psiEquiv.symm (uBarProd κ) = Multiplicative.ofAdd (bvec 10 κ)
  rw [← psi_bvec κ]
  exact psiEquiv.symm_apply_apply _

theorem uCoord_eq_one_iff (g : P0) : uCoord g = 1 ↔ (g : Dfull) ∈ Lgrp := by
  change psiEquiv.symm (QuotientGroup.mk' (Lgrp.subgroupOf P0) g) = 1 ↔ (g : Dfull) ∈ Lgrp
  rw [MulEquiv.map_eq_one_iff]
  change (g : Q) = 1 ↔ (g : Dfull) ∈ Lgrp
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf

theorem uCoord_surjective : Function.Surjective uCoord := by
  change Function.Surjective (psiEquiv.symm ∘ QuotientGroup.mk' (Lgrp.subgroupOf P0))
  exact psiEquiv.symm.surjective.comp (QuotientGroup.mk'_surjective _)


private theorem aMap_zero (k : ℕ) : aMap k 0 = 0 := by
  simp [aMap]

private theorem aMap_add (k : ℕ) (u v : Fin 16 → ZMod 2) :
    aMap k (u + v) = aMap k u + aMap k v := by
  simp only [aMap, Pi.add_apply, add_smul, Finset.sum_add_distrib]

private theorem aMap_basis (k : ℕ) (j : Fin 16) :
    aMap k (bvec 16 (2 ^ (j : ℕ))) =
      bvec 16 ((uConjLN.getD k []).getD (j : ℕ) (0, 0)).1 := by
  rw [aMap, Finset.sum_eq_single j]
  · rw [bvec_apply, Nat.testBit_two_pow]
    simp
  · intro i _ hij
    rw [bvec_apply, Nat.testBit_two_pow]
    have h : (j : ℕ) ≠ (i : ℕ) := fun e => hij (Fin.ext e.symm)
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem uConjL_fst_lt (k j : ℕ) (hk : k < 10) (hj : j < 16) :
    ((uConjLN.getD k []).getD j (0, 0)).1 < 2 ^ 16 := by
  interval_cases k <;> interval_cases j <;> decide +kernel

private theorem sCoord_lD_two_pow (j : ℕ) (hj : j < 16) :
    sCoord ⟨lD (2 ^ j), lD_mem_Lgrp (2 ^ j)⟩ =
      Multiplicative.ofAdd (bvec 16 (2 ^ j)) := by
  have hpow : 2 ^ j < 2 ^ 16 := Nat.pow_lt_pow_right (by norm_num) hj
  have hmem : lD (2 ^ j) * 1 ∈ Lgrp := by simpa using lD_mem_Lgrp (2 ^ j)
  have h := sCoord_lD_mul (σ := 2 ^ j) hpow (t := 1) T9.one_mem hmem
  simpa using h

private noncomputable def conjL (k : ℕ) (hk : k < 10) : Lgrp →* Lgrp where
  toFun y := ⟨uD k * y * (uD k)⁻¹, conj_mem_Lgrp (uD_mem_P0 hk) y.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' y z := by
    apply Subtype.ext
    change uD k * (y * z) * (uD k)⁻¹ =
      (uD k * y * (uD k)⁻¹) * (uD k * z * (uD k)⁻¹)
    group

private noncomputable def psiS (k : ℕ) : Lgrp →* Multiplicative (Fin 16 → ZMod 2) where
  toFun y := Multiplicative.ofAdd (aMap k (sCoord y).toAdd)
  map_one' := by
    simp [aMap_zero]
  map_mul' y z := by
    change Multiplicative.ofAdd (aMap k (sCoord (y * z)).toAdd) =
      Multiplicative.ofAdd (aMap k (sCoord y).toAdd) *
        Multiplicative.ofAdd (aMap k (sCoord z).toAdd)
    rw [map_mul, toAdd_mul, aMap_add]
    rfl

set_option maxHeartbeats 3000000 in
private theorem sCoord_conj_uD (k : ℕ) (hk : k < 10) (y : Lgrp) :
    sCoord ⟨uD k * y * (uD k)⁻¹, conj_mem_Lgrp (uD_mem_P0 hk) y.2⟩ =
      Multiplicative.ofAdd (aMap k (sCoord y).toAdd) := by
  change sCoord (conjL k hk y) = psiS k y
  suffices h : sCoord.comp (conjL k hk) = psiS k by
    exact congrFun (congrArg DFunLike.coe h) y
  apply MonoidHom.ext
  intro z
  obtain ⟨σ, hσ, τ, hτ, hz⟩ := exists_lD_mul_tD z.2
  have hzL : z = (⟨lD σ, lD_mem_Lgrp σ⟩ : Lgrp) *
      ⟨tD τ, T9_le_Lgrp (tD_mem_T9 τ)⟩ := by
    apply Subtype.ext
    exact hz
  rw [hzL, map_mul, map_mul]
  refine congrArg₂ (· * ·) ?_ ?_
  · have hfac : ∀ j < 16,
        sCoord (conjL k hk ⟨lD (2 ^ j), lD_mem_Lgrp (2 ^ j)⟩) =
          psiS k ⟨lD (2 ^ j), lD_mem_Lgrp (2 ^ j)⟩ := by
      intro j hj
      let σ' := ((uConjLN.getD k []).getD j (0, 0)).1
      let τ' := ((uConjLN.getD k []).getD j (0, 0)).2
      have hσ' : σ' < 2 ^ 16 := uConjL_fst_lt k j hk hj
      have hconj : (conjL k hk ⟨lD (2 ^ j), lD_mem_Lgrp (2 ^ j)⟩ : Lgrp) =
          ⟨lD σ' * tD τ', Lgrp.mul_mem (lD_mem_Lgrp σ')
            (T9_le_Lgrp (tD_mem_T9 τ'))⟩ := by
        apply Subtype.ext
        change uD k * lD (2 ^ j) * (uD k)⁻¹ = lD σ' * tD τ'
        rw [uD_mul_lD (k := k) (j := j) hk hj]
        group
        rfl
      rw [hconj]
      rw [show sCoord ⟨lD σ' * tD τ', Lgrp.mul_mem (lD_mem_Lgrp σ')
          (T9_le_Lgrp (tD_mem_T9 τ'))⟩ = Multiplicative.ofAdd (bvec 16 σ') from
        sCoord_lD_mul hσ' (tD_mem_T9 τ') _]
      change Multiplicative.ofAdd (bvec 16 σ') =
        Multiplicative.ofAdd (aMap k (sCoord ⟨lD (2 ^ j), lD_mem_Lgrp (2 ^ j)⟩).toAdd)
      rw [sCoord_lD_two_pow j hj, toAdd_ofAdd, aMap_basis k ⟨j, hj⟩]
    have hsub : (⟨lD σ, lD_mem_Lgrp σ⟩ : Lgrp) =
        ((List.range 16).map fun j => if σ.testBit j then
          (⟨lD (2 ^ j), lD_mem_Lgrp (2 ^ j)⟩ : Lgrp) else 1).prod := by
      apply Subtype.ext
      rw [Subgroup.val_list_prod, List.map_map]
      have hmap : (List.range 16).map (Subtype.val ∘ fun j =>
          if σ.testBit j then (⟨lD (2 ^ j), lD_mem_Lgrp (2 ^ j)⟩ : Lgrp) else 1) =
          (List.range 16).map (fun j => if σ.testBit j then lD (2 ^ j) else 1) := by
        apply List.map_congr_left
        intro j hj
        by_cases h : σ.testBit j <;> simp [h]
      rw [hmap]
      change lD σ = ((List.range 16).map fun j =>
        if σ.testBit j then lD (2 ^ j) else 1).prod
      rw [lD_eq_prod]
    rw [hsub]
    rw [map_list_prod]
    rw [map_list_prod]
    rw [List.map_map, List.map_map]
    refine congrArg List.prod ?_
    apply List.map_congr_left
    intro j hj
    have hj16 := List.mem_range.1 hj
    by_cases h : σ.testBit j
    · simp [h, hfac j hj16]
    · simp [h]
  · change sCoord (conjL k hk ⟨tD τ, T9_le_Lgrp (tD_mem_T9 τ)⟩) =
      psiS k ⟨tD τ, T9_le_Lgrp (tD_mem_T9 τ)⟩
    have hTφ : sCoord (conjL k hk ⟨tD τ, T9_le_Lgrp (tD_mem_T9 τ)⟩) = 1 := by
      rw [sCoord_eq_one_iff]
      change uD k * tD τ * (uD k)⁻¹ ∈ T9
      exact conj_mem_T9 (uD_mem_P0 hk) (tD_mem_T9 τ)
    have hTψ : psiS k ⟨tD τ, T9_le_Lgrp (tD_mem_T9 τ)⟩ = 1 := by
      change Multiplicative.ofAdd (aMap k (sCoord ⟨tD τ, T9_le_Lgrp (tD_mem_T9 τ)⟩).toAdd) = 1
      rw [show sCoord ⟨tD τ, T9_le_Lgrp (tD_mem_T9 τ)⟩ = 1 from
        (sCoord_eq_one_iff _).mpr (tD_mem_T9 τ)]
      simp [aMap_zero]
    rw [hTφ, hTψ]

theorem exists_nf {g : Dfull} (hg : g ∈ P0) :
    ∃ σ < 2 ^ 16, ∃ τ < 2 ^ 9, ∃ κ < 2 ^ 10, g = lD σ * tD τ * uE κ := by
  obtain ⟨κ, hκ, hb⟩ := exists_bvec' 10 (uCoord ⟨g, hg⟩).toAdd
  have hcoord : uCoord ⟨g, hg⟩ = Multiplicative.ofAdd (bvec 10 κ) := by
    rw [hb]
    exact (ofAdd_toAdd (uCoord ⟨g, hg⟩)).symm
  have hone : uCoord (⟨g, hg⟩ * ⟨uE κ, uE_mem_P0 κ⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, hcoord, uCoord_uE, mul_inv_cancel]
  have hmem : ((⟨g, hg⟩ * ⟨uE κ, uE_mem_P0 κ⟩⁻¹ : P0) : Dfull) ∈ Lgrp :=
    (uCoord_eq_one_iff _).mp hone
  obtain ⟨σ, hσ, τ, hτ, hlt⟩ := exists_lD_mul_tD hmem
  refine ⟨σ, hσ, τ, hτ, κ, hκ, ?_⟩
  have hcast : ((⟨g, hg⟩ * ⟨uE κ, uE_mem_P0 κ⟩⁻¹ : P0) : Dfull) =
      g * (uE κ)⁻¹ := rfl
  rw [hcast] at hlt
  calc g = g * (uE κ)⁻¹ * uE κ := by group
    _ = (lD σ * tD τ) * uE κ := by rw [hlt]
    _ = lD σ * tD τ * uE κ := by rfl

theorem tVec_conj (g : P0) {t : Dfull} (ht : t ∈ T9) :
    tVec ((g : Dfull) * t * (g : Dfull)⁻¹) = bAct (uCoord g).toAdd (tVec t) := by
  obtain ⟨σ, hσ, τ, hτ, κ, hκ, hg⟩ := exists_nf g.2
  have hxL : lD σ * tD τ ∈ Lgrp :=
    Lgrp.mul_mem (lD_mem_Lgrp σ) (T9_le_Lgrp (tD_mem_T9 τ))
  have hinner : uE κ * t * (uE κ)⁻¹ ∈ T9 := conj_mem_T9 (uE_mem_P0 κ) ht
  have hxcomm : (lD σ * tD τ) * (uE κ * t * (uE κ)⁻¹) =
      (uE κ * t * (uE κ)⁻¹) * (lD σ * tD τ) :=
    (Subgroup.mem_centralizer_iff.1 (Lgrp_le_centralizer_T9 hxL)
      (uE κ * t * (uE κ)⁻¹) hinner).symm
  have hconj : (g : Dfull) * t * (g : Dfull)⁻¹ = uE κ * t * (uE κ)⁻¹ := by
    rw [hg]
    calc (lD σ * tD τ * uE κ) * t * (lD σ * tD τ * uE κ)⁻¹
        = (lD σ * tD τ) * (uE κ * t * (uE κ)⁻¹) * (lD σ * tD τ)⁻¹ := by group
      _ = (uE κ * t * (uE κ)⁻¹) * (lD σ * tD τ) * (lD σ * tD τ)⁻¹ := by rw [hxcomm]
      _ = uE κ * t * (uE κ)⁻¹ := by group
  have hxP : lD σ * tD τ ∈ P0 := Lgrp_le_P0 hxL
  have huCoord : uCoord g = Multiplicative.ofAdd (bvec 10 κ) := by
    have hx1 : uCoord ⟨lD σ * tD τ, hxP⟩ = 1 :=
      (uCoord_eq_one_iff _).mpr hxL
    have hx2 : uCoord ⟨uE κ, uE_mem_P0 κ⟩ = Multiplicative.ofAdd (bvec 10 κ) :=
      uCoord_uE κ
    have hg' : g = ⟨lD σ * tD τ, hxP⟩ * ⟨uE κ, uE_mem_P0 κ⟩ := by
      apply Subtype.ext
      exact hg
    rw [hg', map_mul, hx1, hx2, one_mul]
  rw [hconj, tVec_conj_uE_bAct κ ht, huCoord, toAdd_ofAdd]


private theorem sCoord_conj_uEl (l : List ℕ) (hl : ∀ k ∈ l, k < 10) (κ : ℕ) (y : Lgrp) :
    sCoord ⟨uEl l κ * y * (uEl l κ)⁻¹, conj_mem_Lgrp (uEl_mem_P0 hl κ) y.2⟩ =
      Multiplicative.ofAdd
        (l.foldr (fun k w => if κ.testBit k then aMap k w else w) (sCoord y).toAdd) := by
  induction l with
  | nil => simp [uEl, wordX_nil]
  | cons a l ih =>
    have hl' : ∀ k ∈ l, k < 10 := fun k hk => hl k (by simp [hk])
    have hmem : uEl l κ ∈ P0 := uEl_mem_P0 hl' κ
    have hy : uEl l κ * y * (uEl l κ)⁻¹ ∈ Lgrp := conj_mem_Lgrp hmem y.2
    have hx : uEl (a :: l) κ * y * (uEl (a :: l) κ)⁻¹ =
        (if κ.testBit a then uD a else 1) * (uEl l κ * y * (uEl l κ)⁻¹) *
          (if κ.testBit a then uD a else 1)⁻¹ := by
      rw [uEl_cons]
      group
    have hmemR : (if κ.testBit a then uD a else 1) *
        (uEl l κ * y * (uEl l κ)⁻¹) * (if κ.testBit a then uD a else 1)⁻¹ ∈ Lgrp := by
      by_cases h : κ.testBit a
      · rw [if_pos h]
        exact conj_mem_Lgrp (uD_mem_P0 (hl a (by simp))) hy
      · rw [if_neg h]
        simpa using hy
    have hxL : (⟨uEl (a :: l) κ * y * (uEl (a :: l) κ)⁻¹,
        conj_mem_Lgrp (uEl_mem_P0 hl κ) y.2⟩ : Lgrp) =
        ⟨(if κ.testBit a then uD a else 1) * (uEl l κ * y * (uEl l κ)⁻¹) *
          (if κ.testBit a then uD a else 1)⁻¹, hmemR⟩ := by
      apply Subtype.ext
      exact hx
    rw [hxL, List.foldr_cons]
    by_cases h : κ.testBit a
    · simp only [h, if_true]
      have hmemA : uD a * (⟨uEl l κ * y * (uEl l κ)⁻¹, hy⟩ : Lgrp) * (uD a)⁻¹ ∈ Lgrp := by
        simpa [h] using hmemR
      have hstep := sCoord_conj_uD a (hl a (by simp))
        (⟨uEl l κ * y * (uEl l κ)⁻¹, hy⟩ : Lgrp)
      calc sCoord ⟨uD a * (uEl l κ * y * (uEl l κ)⁻¹) * (uD a)⁻¹, _⟩
          = sCoord ⟨uD a * (⟨uEl l κ * y * (uEl l κ)⁻¹, hy⟩ : Lgrp) * (uD a)⁻¹,
              hmemA⟩ := by
            apply congrArg sCoord
            apply Subtype.ext
            rfl
        _ = Multiplicative.ofAdd
              (aMap a (sCoord ⟨uEl l κ * y * (uEl l κ)⁻¹, hy⟩).toAdd) := hstep
        _ = Multiplicative.ofAdd
              (aMap a (List.foldr (fun k w => if κ.testBit k then aMap k w else w)
                (sCoord y).toAdd l)) := by
            rw [ih hl', toAdd_ofAdd]
    · simpa [h] using ih hl'

private theorem foldr_range_finRange_a (n : ℕ) (hn : n ≤ 10) (κ : ℕ) (v : Fin 16 → ZMod 2) :
    (List.range n).foldr (fun k w => if κ.testBit k then aMap k w else w) v
      = (List.finRange n).foldr (fun (k : Fin n) w =>
        if (bvec 10 κ) ⟨(k : ℕ), by omega⟩ = 1 then aMap (k : ℕ) w else w) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.finRange_succ_last, List.foldr_append, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil, List.foldr_map, Fin.val_last,
      Fin.val_castSucc]
    have hbit : (bvec 10 κ) ⟨n, by omega⟩ = if κ.testBit n then 1 else 0 := by
      rw [bvec_apply]
    rw [show (if (bvec 10 κ) ⟨n, by omega⟩ = 1 then aMap n v else v) =
        (if κ.testBit n then aMap n v else v) from by
      rw [hbit]
      by_cases h : κ.testBit n <;> simp [h]]
    simpa only [Fin.coe_castSucc] using ih (by omega) (v := if κ.testBit n then aMap n v else v)

private theorem aAct_eq_range_fold (κ : ℕ) (v : Fin 16 → ZMod 2) :
    aAct (bvec 10 κ) v =
      (List.range 10).foldr (fun k w => if κ.testBit k then aMap k w else w) v := by
  rw [aAct]
  simpa only using (foldr_range_finRange_a 10 le_rfl κ v).symm

private theorem sCoord_conj_uE (κ : ℕ) (y : Lgrp) :
    sCoord ⟨uE κ * y * (uE κ)⁻¹, conj_mem_Lgrp (uE_mem_P0 κ) y.2⟩ =
      Multiplicative.ofAdd
        ((List.range 10).foldr (fun k w => if κ.testBit k then aMap k w else w)
          (sCoord y).toAdd) := by
  simpa only [uEl, uE, uProd] using
    sCoord_conj_uEl (List.range 10) (fun k hk => List.mem_range.1 hk) κ y

set_option maxHeartbeats 12000000 in
theorem sCoord_conj (g : P0) (x : Lgrp) :
    sCoord ⟨(g : Dfull) * x * (g : Dfull)⁻¹, conj_mem_Lgrp g.2 x.2⟩ =
      Multiplicative.ofAdd (aAct (uCoord g).toAdd (sCoord x).toAdd) := by
  obtain ⟨σ, hσ, τ, hτ, κ, hκ, hg⟩ := exists_nf g.2
  have hL : lD σ * tD τ ∈ Lgrp :=
    Lgrp.mul_mem (lD_mem_Lgrp σ) (T9_le_Lgrp (tD_mem_T9 τ))
  let l : Lgrp := ⟨lD σ * tD τ, hL⟩
  let z : Lgrp := ⟨uE κ * x * (uE κ)⁻¹, conj_mem_Lgrp (uE_mem_P0 κ) x.2⟩
  have hconjD : (g : Dfull) * x * (g : Dfull)⁻¹ = l * z * l⁻¹ := by
    rw [hg]
    change (lD σ * tD τ * uE κ) * x * (lD σ * tD τ * uE κ)⁻¹ =
      (lD σ * tD τ) * (uE κ * x * (uE κ)⁻¹) * (lD σ * tD τ)⁻¹
    group
  have hconj : (⟨(g : Dfull) * x * (g : Dfull)⁻¹, conj_mem_Lgrp g.2 x.2⟩ : Lgrp) =
      l * z * l⁻¹ := by
    apply Subtype.ext
    exact hconjD
  rw [hconj, map_mul, map_mul, map_inv]
  have hz : sCoord z = Multiplicative.ofAdd
      ((List.range 10).foldr (fun k w => if κ.testBit k then aMap k w else w)
        (sCoord x).toAdd) := sCoord_conj_uE κ x
  rw [hz]
  have hxP : lD σ * tD τ ∈ P0 := Lgrp_le_P0 hL
  have hu : uCoord g = Multiplicative.ofAdd (bvec 10 κ) := by
    have hg' : g = (⟨lD σ * tD τ, hxP⟩ : P0) * ⟨uE κ, uE_mem_P0 κ⟩ := by
      apply Subtype.ext
      exact hg
    rw [hg', map_mul]
    have h1 : uCoord ⟨lD σ * tD τ, hxP⟩ = 1 := (uCoord_eq_one_iff _).mpr hL
    rw [h1, uCoord_uE, one_mul]
  rw [hu, toAdd_ofAdd, aAct_eq_range_fold, mul_comm (sCoord l), mul_inv_cancel_right]



end CFSG.Monster.B.TwoA.Sp8.WordRel

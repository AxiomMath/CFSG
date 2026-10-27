module

public import CFSG.Monster.B.TwoA.Sp8.P0UCoord
public import CFSG.Monster.B.TwoA.Sp8.P0RankInputs
public import CFSG.Monster.B.TwoA.Sp8.P0RankLin

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix
open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank


private theorem bvec_colsAct (m : ℕ) (cs : List ℕ) (σ : ℕ) :
    bvec m (colsAct cs σ) =
      ∑ j : Fin cs.length, (bvec cs.length σ j) • bvec m (cs.getD (j : ℕ) 0) := by
  induction cs generalizing σ m with
  | nil => simp [colsAct, bvec_zero]
  | cons c cs ih =>
      rw [colsAct, bvec_xor, ih m (σ / 2)]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      have hfirst : bvec m (if σ % 2 = 1 then c else 0) =
          (bvec (cs.length + 1) σ 0) • bvec m c := by
        rcases Nat.mod_two_eq_zero_or_one σ with h | h
        · simp [h, bvec_zero, bvec_apply, Nat.testBit_zero]
        · simp [h, bvec_apply, Nat.testBit_zero]
      rw [hfirst]
      simp only [Fin.val_zero, List.getD_cons_zero]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro i _
      have hb : bvec (cs.length + 1) σ i.succ = bvec cs.length (σ / 2) i := by
        rw [bvec_apply, bvec_apply, Fin.val_succ, Nat.testBit_succ]
      have hg : (c :: cs).getD (i.succ : ℕ) 0 = cs.getD (i : ℕ) 0 := by
        rw [Fin.val_succ, List.getD_cons_succ]
      rw [hb, hg]

private theorem bvec_colsAct_eq_sum {m n : ℕ} {cs : List ℕ} (hn : cs.length = n) (σ : ℕ) :
    bvec m (colsAct cs σ) =
      ∑ j : Fin n, (bvec n σ j) • bvec m (cs.getD (j : ℕ) 0) := by
  subst n
  exact bvec_colsAct m cs σ

private theorem aCols_getD (k : ℕ) :
    p0Data.aCols.getD k [] = (uConjLN.getD k []).map (·.1) := by
  change (uConjLN.map (fun x => x.map (fun x => x.1))).getD k [] =
    (uConjLN.getD k []).map (fun x => x.1)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases h : uConjLN[k]? <;> rfl

private theorem aCols_getD_entry (k j : ℕ) (hk : k < 10) (hj : j < 16) :
    (p0Data.aCols.getD k []).getD j 0 =
      ((uConjLN.getD k []).getD j (0, 0)).1 := by
  have _ := hk
  have _ := hj
  rw [aCols_getD]
  conv_lhs => rw [show (0 : ℕ) = (fun p : ℕ × ℕ => p.1) (0, 0) from rfl]
  rw [List.getD_map]

private theorem uConjLN_length (k : ℕ) (hk : k < 10) :
    (uConjLN.getD k []).length = 16 := by
  interval_cases k <;> decide

private theorem uConjTN_length (k : ℕ) (hk : k < 10) :
    (uConjTN.getD k []).length = 9 := by
  interval_cases k <;> decide

private theorem aCols_length (k : ℕ) (hk : k < 10) :
    (p0Data.aCols.getD k []).length = 16 := by
  rw [aCols_getD, List.length_map, uConjLN_length k hk]

private theorem bvec_colsAct_aCols (k : ℕ) (hk : k < 10) (σ : ℕ) :
    bvec 16 (colsAct (p0Data.aCols.getD k []) σ) = aMap k (bvec 16 σ) := by
  rw [bvec_colsAct_eq_sum (aCols_length k hk)]
  rw [aMap]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [aCols_getD_entry k j hk j.2]

private theorem bvec_colsAct_uConjT (k : ℕ) (hk : k < 10) (τ : ℕ) :
    bvec 9 (colsAct (p0Data.uConjT.getD k []) τ) = bMap k (bvec 9 τ) := by
  have hlen : (p0Data.uConjT.getD k []).length = 9 := uConjTN_length k hk
  rw [bvec_colsAct_eq_sum hlen]
  rw [bMap]
  rfl

private theorem bvec_foldr_range (m n : ℕ) (G : ℕ → ℕ → ℕ)
    (F : Fin n → (Fin m → ZMod 2) → (Fin m → ZMod 2))
    (hG : ∀ k (hk : k < n) (x : ℕ), bvec m (G k x) = F ⟨k, hk⟩ (bvec m x))
    (x : ℕ) :
    bvec m ((List.range n).foldr G x) = (List.finRange n).foldr F (bvec m x) := by
  rw [← List.map_coe_finRange_eq_range, List.foldr_map]
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldr_cons, List.foldr_cons, hG (a : ℕ) a.2, ih]

private theorem bvec_actK_aCols_aux (κ σ : ℕ) :
    bvec 16 (actK p0Data.aCols κ σ) =
      (List.finRange 10).foldr
        (fun k w => if bvec 10 κ k = 1 then aMap k w else w) (bvec 16 σ) := by
  rw [actK]
  have hlen : p0Data.aCols.length = 10 := by decide
  rw [hlen]
  refine bvec_foldr_range 16 10
    (fun k y => if κ.testBit k then colsAct (p0Data.aCols.getD k []) y else y)
    (fun k w => if bvec 10 κ k = 1 then aMap k w else w) ?_ σ
  intro k hk x
  by_cases h : κ.testBit k
  · rw [if_pos h]
    have hk1 : bvec 10 κ ⟨k, hk⟩ = 1 := by rw [bvec_apply, if_pos h]
    rw [if_pos hk1, bvec_colsAct_aCols k hk x]
  · rw [if_neg h]
    have hk0 : bvec 10 κ ⟨k, hk⟩ ≠ 1 := by rw [bvec_apply, if_neg h]; decide
    rw [if_neg hk0]

private theorem bvec_actK_uConjT_aux (κ τ : ℕ) :
    bvec 9 (actK p0Data.uConjT κ τ) =
      (List.finRange 10).foldr
        (fun k w => if bvec 10 κ k = 1 then bMap k w else w) (bvec 9 τ) := by
  rw [actK]
  have hlen : p0Data.uConjT.length = 10 := by decide
  rw [hlen]
  refine bvec_foldr_range 9 10
    (fun k y => if κ.testBit k then colsAct (p0Data.uConjT.getD k []) y else y)
    (fun k w => if bvec 10 κ k = 1 then bMap k w else w) ?_ τ
  intro k hk x
  by_cases h : κ.testBit k
  · rw [if_pos h]
    have hk1 : bvec 10 κ ⟨k, hk⟩ = 1 := by rw [bvec_apply, if_pos h]
    rw [if_pos hk1, bvec_colsAct_uConjT k hk x]
  · rw [if_neg h]
    have hk0 : bvec 10 κ ⟨k, hk⟩ ≠ 1 := by rw [bvec_apply, if_neg h]; decide
    rw [if_neg hk0]

private theorem lCommN_length : lCommN.length = 16 := by decide

private theorem lCommN_entry_lt :
    ∀ row ∈ lCommN, ∀ c ∈ row, c < 2 ^ 9 := by decide

private theorem getD_mem_of_lt {α : Type*} {l : List α} {d : α} {j : ℕ}
    (hj : j < l.length) : l.getD j d ∈ l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

private theorem colsAct_take_lt (j : ℕ) (hj : j < 16) (σ : ℕ) :
    colsAct ((p0Data.beta.getD j []).take j) σ < 2 ^ 9 := by
  apply colsAct_lt
  intro c hc
  have hmem : p0Data.beta.getD j [] ∈ p0Data.beta := by
    rw [show p0Data.beta = lCommN from rfl]
    exact getD_mem_of_lt (by rw [lCommN_length]; exact hj)
  exact lCommN_entry_lt _ (by simpa [show p0Data.beta = lCommN from rfl] using hmem) c
    (List.mem_of_mem_take hc)

private theorem foldl_xor_lt {m : ℕ} (l : List ℕ) (f : ℕ → ℕ → ℕ) (acc : ℕ)
    (hacc : acc < 2 ^ m)
    (hf : ∀ a ∈ l, ∀ x, x < 2 ^ m → f x a < 2 ^ m) :
    l.foldl f acc < 2 ^ m := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons a l ih =>
      rw [List.foldl_cons]
      exact ih (f acc a) (hf a (by simp) acc hacc)
        (fun b hb x hx => hf b (by simp [hb]) x hx)

private theorem lCommN_row_length (i : ℕ) (hi : i < 16) :
    (lCommN.getD i []).length = 16 := by
  interval_cases i <;> decide

private theorem foldl_congr {α β : Type*} {l : List α} {f g : β → α → β} {b : β}
    (h : ∀ a ∈ l, ∀ x, f x a = g x a) : l.foldl f b = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldl_cons, List.foldl_cons, h a (by simp) b]
      exact ih (fun a ha x => h a (by simp [ha]) x)

private theorem bvec_foldl_xor (m : ℕ) (l : List ℕ) (g : ℕ → ℕ) (acc : ℕ) :
    bvec m (l.foldl (fun acc j => acc ^^^ g j) acc) =
      bvec m acc + (l.map (fun j => bvec m (g j))).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
      rw [List.foldl_cons, ih (acc ^^^ g a), bvec_xor, List.map_cons, List.sum_cons]
      abel

private theorem list_sum_range_eq_finset_sum {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    (List.map f (List.range n)).sum = ∑ i ∈ Finset.range n, f i := by
  rw [← List.sum_toFinset f List.nodup_range, List.toFinset_range]

private theorem sum_fin_ite_lt {M : Type*} [AddCommMonoid M] {n : ℕ}
    (j : Fin n) (f : Fin n → M) :
    (∑ i : Fin n, if i < j then f i else 0) =
      ∑ i : Fin j, f (Fin.castLE (Nat.le_of_lt j.2) i) := by
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.sum_fin_eq_sum_range]
  have hL : (∑ i ∈ Finset.range n, if h : i < n then
      (if (⟨i, h⟩ : Fin n) < j then f ⟨i, h⟩ else 0) else 0) =
    ∑ i ∈ Finset.range n, if i < (j : ℕ) then
      (if h : i < n then f ⟨i, h⟩ else 0) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < n := Finset.mem_range.1 hi
    rw [dif_pos hi']
    by_cases hij : i < (j : ℕ)
    · have hfin : (⟨i, hi'⟩ : Fin n) < j := by rwa [Fin.lt_def]
      rw [if_pos hfin, if_pos hij, dif_pos hi']
    · have hfin : ¬ (⟨i, hi'⟩ : Fin n) < j := by rwa [Fin.lt_def]
      rw [if_neg hfin, if_neg hij]
  rw [hL, ← Finset.sum_filter]
  have hfilter : (Finset.range n).filter (fun i => i < (j : ℕ)) = Finset.range (j : ℕ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hij : i < (j : ℕ) := Finset.mem_range.1 hi
  have hin : i < n := lt_of_lt_of_le hij (le_of_lt j.2)
  rw [dif_pos hin, dif_pos hij]
  exact congrArg f (Fin.ext rfl)


theorem actK_aCols_lt (κ : ℕ) {σ : ℕ} (hσ : σ < 2 ^ 16) : actK p0Data.aCols κ σ < 2 ^ 16 := by
  have h : ∀ cs ∈ p0Data.aCols, ∀ c ∈ cs, c < 2 ^ 16 := by decide
  exact actK_lt h κ hσ

theorem bvec_actK_aCols (κ : ℕ) {σ : ℕ} (hσ : σ < 2 ^ 16) :
    bvec 16 (actK p0Data.aCols κ σ) = aAct (bvec 10 κ) (bvec 16 σ) := by
  have _ := hσ
  rw [bvec_actK_aCols_aux, aAct]

theorem actK_uConjT_lt (κ : ℕ) {τ : ℕ} (hτ : τ < 2 ^ 9) : actK p0Data.uConjT κ τ < 2 ^ 9 := by
  have h : ∀ cs ∈ p0Data.uConjT, ∀ c ∈ cs, c < 2 ^ 9 := by decide
  exact actK_lt h κ hτ

theorem bvec_actK_uConjT (κ : ℕ) {τ : ℕ} (hτ : τ < 2 ^ 9) :
    bvec 9 (actK p0Data.uConjT κ τ) = bAct (bvec 10 κ) (bvec 9 τ) := by
  have _ := hτ
  rw [bvec_actK_uConjT_aux, bAct]

theorem qN_lt (σ : ℕ) : MonsterB.P0Rank.qN p0Data.beta σ < 2 ^ 9 := by
  change (List.range 16).foldl
    (fun acc j => if σ.testBit j then acc ^^^ colsAct ((p0Data.beta.getD j []).take j) σ
      else acc) 0 < 2 ^ 9
  refine foldl_xor_lt (List.range 16)
    (fun acc j => if σ.testBit j then acc ^^^ colsAct ((p0Data.beta.getD j []).take j) σ
      else acc) 0 (by norm_num) ?_
  intro j hj acc hacc
  rw [List.mem_range] at hj
  by_cases h : σ.testBit j
  · rw [if_pos h]
    exact Nat.xor_lt_two_pow hacc (colsAct_take_lt j hj σ)
  · rw [if_neg h]
    exact hacc

theorem bvec_qN {σ : ℕ} (hσ : σ < 2 ^ 16) :
    bvec 9 (MonsterB.P0Rank.qN p0Data.beta σ) = lQuad (bvec 16 σ) := by
  have _ := hσ
  change bvec 9 ((List.range 16).foldl
    (fun acc j => if σ.testBit j then acc ^^^ colsAct ((p0Data.beta.getD j []).take j) σ
      else acc) 0) = lQuad (bvec 16 σ)
  rw [show p0Data.beta = lCommN from rfl]
  have hfold : ((List.range 16).foldl
      (fun acc j => if σ.testBit j then acc ^^^ colsAct ((lCommN.getD j []).take j) σ
        else acc) 0) =
      ((List.range 16).foldl
      (fun acc j => acc ^^^ (if σ.testBit j then
        colsAct ((lCommN.getD j []).take j) σ else 0)) 0) := by
    refine foldl_congr ?_
    intro a ha x
    by_cases h : σ.testBit a <;> simp [h]
  rw [hfold]
  · rw [bvec_foldl_xor, bvec_zero, zero_add]
    rw [list_sum_range_eq_finset_sum, ← Fin.sum_univ_eq_sum_range]
    rw [lQuad, Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hbit : σ.testBit j
    · rw [if_pos hbit]
      have hlen : ((lCommN.getD (j : ℕ) []).take (j : ℕ)).length = (j : ℕ) := by
        rw [List.length_take, lCommN_row_length j j.2]
        omega
      rw [bvec_colsAct_eq_sum (m := 9) (n := (j : ℕ))
        (cs := (lCommN.getD (j : ℕ) []).take (j : ℕ)) hlen σ]
      have hbvecj : bvec 16 σ j = 1 := by rw [bvec_apply, if_pos hbit]
      rw [hbvecj]
      simp only [mul_one]
      rw [sum_fin_ite_lt j (fun i => bvec 16 σ i •
        bvec 9 ((lCommN.getD (j : ℕ) []).getD (i : ℕ) 0))]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hb : bvec (j : ℕ) σ i = bvec 16 σ (Fin.castLE (Nat.le_of_lt j.2) i) := by
        rw [bvec_apply, bvec_apply, Fin.val_castLE]
      have hg : ((lCommN.getD (j : ℕ) []).take (j : ℕ)).getD (i : ℕ) 0 =
          (lCommN.getD (j : ℕ) []).getD
            ((Fin.castLE (Nat.le_of_lt j.2) i : Fin 16) : ℕ) 0 := by
        rw [Fin.val_castLE]
        have h1 : (i : ℕ) < ((lCommN.getD (j : ℕ) []).take (j : ℕ)).length := by
          rw [List.length_take, lCommN_row_length j j.2]
          omega
        have h2 : (i : ℕ) < (lCommN.getD (j : ℕ) []).length := by
          rw [lCommN_row_length j j.2]
          omega
        rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2, List.getElem_take]
      rw [hb, hg]
    · rw [if_neg hbit]
      rw [bvec_zero]
      rw [show bvec 16 σ j = 0 from by rw [bvec_apply, if_neg hbit]]
      simp

theorem betaN_lt (σ δ : ℕ) : MonsterB.P0Rank.betaN p0Data.beta σ δ < 2 ^ 9 := by
  rw [betaN]
  apply colsAct_lt
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  rw [List.mem_range] at hi
  exact colsAct_lt (fun d hd => lCommN_entry_lt _ (by
    rw [show p0Data.beta = lCommN from rfl]
    exact getD_mem_of_lt (by rw [lCommN_length]; exact hi)) d hd) δ

theorem bvec_betaN {σ δ : ℕ} (hσ : σ < 2 ^ 16) (hδ : δ < 2 ^ 16) :
    bvec 9 (MonsterB.P0Rank.betaN p0Data.beta σ δ) = lBeta (bvec 16 σ) (bvec 16 δ) := by
  have _ := hσ
  have _ := hδ
  change bvec 9 (colsAct ((List.range 16).map fun i =>
    colsAct ((p0Data.beta.getD i [])) δ) σ) = lBeta (bvec 16 σ) (bvec 16 δ)
  rw [show p0Data.beta = lCommN from rfl]
  rw [bvec_colsAct_eq_sum (m := 9) (n := 16)
    (cs := (List.range 16).map fun i => colsAct ((lCommN.getD i [])) δ) (by simp) σ]
  rw [lBeta]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hrow : ((List.range 16).map fun i =>
      colsAct ((lCommN.getD i [])) δ).getD (i : ℕ) 0
      = colsAct ((lCommN.getD i [])) δ := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    rw [List.getElem_map, List.getElem_range]
  rw [hrow]
  rw [bvec_colsAct_eq_sum (m := 9) (n := 16) (cs := lCommN.getD (i : ℕ) [])
    (lCommN_row_length i i.2) δ]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [smul_smul]

theorem aAct_add (u u' : Fin 10 → ZMod 2) (v : Fin 16 → ZMod 2) :
    aAct (u + u') v = aAct u (aAct u' v) := by
  obtain ⟨g, hg⟩ := uCoord_surjective (Multiplicative.ofAdd u)
  obtain ⟨g', hg'⟩ := uCoord_surjective (Multiplicative.ofAdd u')
  obtain ⟨y, hy⟩ := sCoord_surjective (Multiplicative.ofAdd v)
  let y' : Lgrp := ⟨(g' : Dfull) * y * (g' : Dfull)⁻¹, conj_mem_Lgrp g'.2 y.2⟩
  have hy' : sCoord y' = Multiplicative.ofAdd (aAct u' v) := by
    dsimp only [y']
    rw [sCoord_conj g' y, hg', hy, toAdd_ofAdd, toAdd_ofAdd]
  have h1 : sCoord ⟨(g * g' : P0) * y * ((g * g' : P0))⁻¹,
      conj_mem_Lgrp (g * g').2 y.2⟩ =
      Multiplicative.ofAdd (aAct (u + u') v) := by
    have hU : (uCoord (g * g')).toAdd = u + u' := by
      rw [map_mul, hg, hg', ← ofAdd_add, toAdd_ofAdd]
    calc sCoord ⟨(g * g' : P0) * y * ((g * g' : P0))⁻¹, conj_mem_Lgrp (g * g').2 y.2⟩
        = Multiplicative.ofAdd (aAct (uCoord (g * g')).toAdd (sCoord y).toAdd) :=
          sCoord_conj (g * g') y
      _ = Multiplicative.ofAdd (aAct (u + u') v) := by rw [hU, hy, toAdd_ofAdd]
  have h2 : sCoord ⟨(g * g' : P0) * y * ((g * g' : P0))⁻¹,
      conj_mem_Lgrp (g * g').2 y.2⟩ =
      Multiplicative.ofAdd (aAct u (aAct u' v)) := by
    have hsame : (⟨((g : P0) * g' : P0) * y * (((g : P0) * g' : P0))⁻¹,
        conj_mem_Lgrp (g * g').2 y.2⟩ : Lgrp) =
        ⟨(g : Dfull) * y' * (g : Dfull)⁻¹, conj_mem_Lgrp g.2 y'.2⟩ := by
      apply Subtype.ext
      dsimp only [y']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    calc sCoord ⟨(g * g' : P0) * y * ((g * g' : P0))⁻¹, conj_mem_Lgrp (g * g').2 y.2⟩
        = sCoord ⟨(g : Dfull) * y' * (g : Dfull)⁻¹, conj_mem_Lgrp g.2 y'.2⟩ := by rw [hsame]
      _ = Multiplicative.ofAdd (aAct (uCoord g).toAdd (sCoord y').toAdd) := sCoord_conj g y'
      _ = Multiplicative.ofAdd (aAct u (aAct u' v)) := by
          rw [hg, hy', toAdd_ofAdd, toAdd_ofAdd]
  exact Multiplicative.ofAdd.injective (h1.symm.trans h2)

theorem bAct_add (u u' : Fin 10 → ZMod 2) (v : Fin 9 → ZMod 2) :
    bAct (u + u') v = bAct u (bAct u' v) := by
  obtain ⟨g, hg⟩ := uCoord_surjective (Multiplicative.ofAdd u)
  obtain ⟨g', hg'⟩ := uCoord_surjective (Multiplicative.ofAdd u')
  obtain ⟨τ, hτ, hb⟩ := CFSG.KC.BvecLoop.exists_bvec 9 v
  let t : Dfull := tD τ
  have ht : t ∈ T9 := tD_mem_T9 τ
  have htv : tVec t = v := by
    rw [show t = tD τ from rfl, tVec_tD, hb]
  let t' : Dfull := (g' : Dfull) * t * (g' : Dfull)⁻¹
  have ht' : t' ∈ T9 := conj_mem_T9 g'.2 ht
  have htv' : tVec t' = bAct u' v := by
    dsimp only [t']
    rw [tVec_conj g' ht, hg', htv, toAdd_ofAdd]
  have h1 : tVec ((g * g' : P0) * t * ((g * g' : P0))⁻¹) = bAct (u + u') v := by
    have hU : (uCoord (g * g')).toAdd = u + u' := by
      rw [map_mul, hg, hg', ← ofAdd_add, toAdd_ofAdd]
    calc tVec ((g * g' : P0) * t * ((g * g' : P0))⁻¹)
        = bAct (uCoord (g * g')).toAdd (tVec t) := tVec_conj (g * g') ht
      _ = bAct (u + u') v := by rw [hU, htv]
  have h2 : tVec ((g * g' : P0) * t * ((g * g' : P0))⁻¹) = bAct u (bAct u' v) := by
    have hsame : ((g * g' : P0) * t * ((g * g' : P0))⁻¹) =
        (g : Dfull) * t' * (g : Dfull)⁻¹ := by
      dsimp only [t']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hU : (uCoord g).toAdd = u := by rw [hg, toAdd_ofAdd]
    calc tVec ((g * g' : P0) * t * ((g * g' : P0))⁻¹)
        = tVec ((g : Dfull) * t' * (g : Dfull)⁻¹) := by rw [hsame]
      _ = bAct (uCoord g).toAdd (tVec t') := tVec_conj g ht'
      _ = bAct u (bAct u' v) := by rw [hU, htv']
  exact h1.symm.trans h2

theorem actK_aCols_xor : ∀ κ < 2 ^ 10, ∀ κ' < 2 ^ 10, ∀ x < 2 ^ 16,
    actK p0Data.aCols (κ ^^^ κ') x = actK p0Data.aCols κ (actK p0Data.aCols κ' x) := by
  intro κ hκ κ' hκ' x hx
  refine CFSG.KC.BvecLoop.bvec_inj (n := 16) ?_ ?_ ?_
  · exact actK_aCols_lt (κ ^^^ κ') hx
  · exact actK_aCols_lt κ (actK_aCols_lt κ' hx)
  · rw [bvec_actK_aCols (κ ^^^ κ') hx,
      bvec_actK_aCols κ (actK_aCols_lt κ' hx),
      bvec_actK_aCols κ' hx, bvec_xor, aAct_add]

theorem actK_uConjT_xor : ∀ κ < 2 ^ 10, ∀ κ' < 2 ^ 10, ∀ x < 2 ^ 9,
    actK p0Data.uConjT (κ ^^^ κ') x = actK p0Data.uConjT κ (actK p0Data.uConjT κ' x) := by
  intro κ hκ κ' hκ' x hx
  refine CFSG.KC.BvecLoop.bvec_inj (n := 9) ?_ ?_ ?_
  · exact actK_uConjT_lt (κ ^^^ κ') hx
  · exact actK_uConjT_lt κ (actK_uConjT_lt κ' hx)
  · rw [bvec_actK_uConjT (κ ^^^ κ') hx,
      bvec_actK_uConjT κ (actK_uConjT_lt κ' hx),
      bvec_actK_uConjT κ' hx, bvec_xor, bAct_add]

@[expose] def factHolds : Fact → Prop
  | .sq κ s t => uE κ * uE κ = lD s * tD t
  | .comm κ κ' s t => uE κ * uE κ' = lD s * tD t * uE κ' * uE κ
  | .conj κ δ c => uE κ * lD δ = lD δ * tD c * uE κ

theorem holds_of_factsCheck {F : List Fact} (h : factsCheck F = true) {f : Fact} (hf : f ∈ F) :
    factBounds f = true ∧ factHolds f := by
  rw [factsCheck, List.all_eq_true] at h
  have hf' := h f hf
  rw [Bool.and_eq_true] at hf'
  obtain ⟨hb, hr⟩ := hf'
  refine ⟨hb, ?_⟩
  cases f with
  | sq κ s t =>
      have hr' : relCheck (uProd κ ++ uProd κ) (lWord s ++ tWord t) = true := by
        simpa [factWords] using hr
      have hw := wordX_eq_of_relCheck hr'
      simpa [factHolds, uE, lD, tD, wordX_append, mul_assoc] using hw
  | comm κ κ' s t =>
      have hr' : relCheck (uProd κ ++ uProd κ')
          (lWord s ++ tWord t ++ uProd κ' ++ uProd κ) = true := by
        simpa [factWords] using hr
      have hw := wordX_eq_of_relCheck hr'
      simpa [factHolds, uE, lD, tD, wordX_append, mul_assoc] using hw
  | conj κ δ c =>
      have hr' : relCheck (uProd κ ++ lWord δ) (lWord δ ++ tWord c ++ uProd κ) = true := by
        simpa [factWords] using hr
      have hw := wordX_eq_of_relCheck hr'
      simpa [factHolds, uE, lD, tD, wordX_append, mul_assoc] using hw

theorem findSq_spec {F : List Fact} {κ s : ℕ} (h : findSq F κ = some s) :
    ∃ t, Fact.sq κ s t ∈ F := by
  unfold findSq at h
  obtain ⟨f, hf, hg⟩ := List.exists_of_findSome?_eq_some h
  cases f with
  | sq a s' t =>
      by_cases hκ : a = κ
      · simp [hκ] at hg
        rw [hκ, hg] at hf
        exact ⟨t, hf⟩
      · simp [hκ] at hg
  | comm _ _ _ _ => simp at hg
  | conj _ _ _ => simp at hg

theorem findComm_spec {F : List Fact} {κ κ' s : ℕ} (h : findComm F κ κ' = some s) :
    ∃ t, Fact.comm κ κ' s t ∈ F := by
  unfold findComm at h
  obtain ⟨f, hf, hg⟩ := List.exists_of_findSome?_eq_some h
  cases f with
  | comm a b s' t =>
      by_cases hκ : a = κ ∧ b = κ'
      · simp [hκ] at hg
        obtain ⟨rfl, rfl⟩ := hκ
        rw [hg] at hf
        exact ⟨t, hf⟩
      · simp [hκ] at hg
  | sq _ _ _ => simp at hg
  | conj _ _ _ => simp at hg

theorem findConj_spec {F : List Fact} {κ δ c : ℕ} (h : findConj F κ δ = some c) :
    Fact.conj κ δ c ∈ F := by
  unfold findConj at h
  obtain ⟨f, hf, hg⟩ := List.exists_of_findSome?_eq_some h
  cases f with
  | conj a d c' =>
      by_cases hκ : a = κ ∧ d = δ
      · simp [hκ] at hg
        obtain ⟨rfl, rfl⟩ := hκ
        rw [hg] at hf
        exact hf
      · simp [hκ] at hg
  | sq _ _ _ => simp at hg
  | comm _ _ _ _ => simp at hg

end CFSG.Monster.B.TwoA.Sp8.WordRel

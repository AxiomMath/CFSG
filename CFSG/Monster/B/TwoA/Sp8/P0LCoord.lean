module

public import CFSG.Monster.B.TwoA.Sp8.P0Words

set_option linter.unusedSectionVars false

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix
open scoped commutatorElement


@[expose] def lBeta (v w : Fin 16 → ZMod 2) : Fin 9 → ZMod 2 :=
  ∑ i : Fin 16, ∑ j : Fin 16, (v i * w j) • bvec 9 ((lCommN.getD i []).getD j 0)

@[expose] def lQuad (v : Fin 16 → ZMod 2) : Fin 9 → ZMod 2 :=
  ∑ i : Fin 16, ∑ j : Fin 16, if i < j then (v i * v j) • bvec 9 ((lCommN.getD j []).getD i 0)
    else 0

@[expose] def tVec (t : Dfull) : Fin 9 → ZMod 2 :=
  haveI := Classical.propDecidable (t ∈ T9)
  if h : t ∈ T9 then Multiplicative.toAdd (tEquiv.symm ⟨t, h⟩) else 0

theorem tVec_tD (τ : ℕ) : tVec (tD τ) = bvec 9 τ := by
  have ht : tD τ ∈ T9 := tD_mem_T9 τ
  unfold tVec
  rw [dif_pos ht]
  have h : tEquiv.symm ⟨tD τ, ht⟩ = Multiplicative.ofAdd (bvec 9 τ) := by
    apply tEquiv.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [coe_tEquiv, toAdd_ofAdd, ← tD_eq]
  rw [h]
  exact toAdd_ofAdd _

theorem tVec_mul {t t' : Dfull} (ht : t ∈ T9) (ht' : t' ∈ T9) :
    tVec (t * t') = tVec t + tVec t' := by
  have hmem : t * t' ∈ T9 := T9.mul_mem ht ht'
  have hprod : (⟨t * t', hmem⟩ : T9) = ⟨t, ht⟩ * ⟨t', ht'⟩ := rfl
  unfold tVec
  rw [dif_pos hmem, dif_pos ht, dif_pos ht']
  have h : tEquiv.symm ⟨t * t', hmem⟩ =
      tEquiv.symm ⟨t, ht⟩ * tEquiv.symm ⟨t', ht'⟩ := by
    rw [← map_mul, hprod]
  rw [h, toAdd_mul]

theorem eq_of_tVec_eq {t t' : Dfull} (ht : t ∈ T9) (ht' : t' ∈ T9) (h : tVec t = tVec t') :
    t = t' := by
  have key : ∀ {u : Dfull} (hu : u ∈ T9), (tEquiv (Multiplicative.ofAdd (tVec u)) : Dfull) = u := by
    intro u hu
    unfold tVec
    rw [dif_pos hu, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  calc t = (tEquiv (Multiplicative.ofAdd (tVec t)) : Dfull) := (key ht).symm
    _ = (tEquiv (Multiplicative.ofAdd (tVec t')) : Dfull) := by rw [h]
    _ = t' := key ht'

private theorem T9_mul_comm {a b : Dfull} (ha : a ∈ T9) (hb : b ∈ T9) : a * b = b * a :=
  congrArg Subtype.val (T9_comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem tVec_one : tVec (1 : Dfull) = 0 := by
  unfold tVec
  rw [dif_pos T9.one_mem]
  have h : (⟨(1 : Dfull), T9.one_mem⟩ : T9) = 1 := rfl
  rw [h, map_one, toAdd_one]

private def tOf (v : Fin 9 → ZMod 2) : Dfull := tEquiv (Multiplicative.ofAdd v)

private theorem tOf_mem_T9 (v : Fin 9 → ZMod 2) : tOf v ∈ T9 := (tEquiv _).2

private theorem tOf_zero : tOf 0 = (1 : Dfull) := by
  unfold tOf
  rw [ofAdd_zero, map_one, Subgroup.coe_one]

private theorem tOf_add (v w : Fin 9 → ZMod 2) : tOf (v + w) = tOf v * tOf w := by
  unfold tOf
  rw [ofAdd_add, map_mul, Subgroup.coe_mul]

private theorem tOf_comm (v w : Fin 9 → ZMod 2) : tOf v * tOf w = tOf w * tOf v :=
  T9_mul_comm (tOf_mem_T9 v) (tOf_mem_T9 w)

private theorem tVec_tOf (v : Fin 9 → ZMod 2) : tVec (tOf v) = v := by
  unfold tVec
  rw [dif_pos (tOf_mem_T9 v)]
  have h : (⟨tOf v, tOf_mem_T9 v⟩ : T9) = tEquiv (Multiplicative.ofAdd v) := rfl
  rw [h, MulEquiv.symm_apply_apply, toAdd_ofAdd]

private theorem tOf_injective : Function.Injective tOf := by
  intro v w h
  have hv := congrArg tVec h
  rwa [tVec_tOf, tVec_tOf] at hv

private theorem tOf_eq_tD (τ : ℕ) : tOf (bvec 9 τ) = tD τ := by
  unfold tOf
  rw [tD_eq, coe_tEquiv, toAdd_ofAdd]

private theorem lD_comm_T9 (σ : ℕ) {t : Dfull} (ht : t ∈ T9) :
    lD σ * t = t * lD σ := by
  have hmem : (⟨t, T9_le_Lgrp ht⟩ : Lgrp) ∈ T9.subgroupOf Lgrp :=
    Subgroup.mem_subgroupOf.2 ht
  have h := Subgroup.mem_center_iff.1 (T9_le_center_Lgrp hmem) ⟨lD σ, lD_mem_Lgrp σ⟩
  exact congrArg Subtype.val h

private theorem tVec_list_prod {l : List Dfull} (hl : ∀ x ∈ l, x ∈ T9) :
    tVec l.prod = (l.map tVec).sum := by
  induction l with
  | nil => simp [tVec_one]
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons, tVec_mul (hl a (List.mem_cons_self ..))
      (list_prod_mem fun x hx => hl x (List.mem_cons_of_mem _ hx)),
      ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]

private theorem lD_eq_prod_range (n : ℕ) (hn : n ≤ 16) {σ : ℕ} (hσ : σ < 2 ^ n) :
    lD σ = ((List.range n).map fun j => if σ.testBit j then lD (2 ^ j) else 1).prod := by
  rw [lD_eq_prod]
  have hrange : List.range 16 = List.range n ++ List.range' n (16 - n) := by
    rw [List.range_eq_range' (n := 16), List.range_eq_range' (n := n)]
    have h := List.range'_append (s := 0) (m := n) (n := 16 - n) (step := 1)
    simpa [show n + (16 - n) = 16 by omega] using h.symm
  rw [hrange, List.map_append, List.prod_append]
  have htail : ((List.range' n (16 - n)).map
      (fun j => if σ.testBit j then lD (2 ^ j) else 1)).prod = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    rw [if_neg]
    intro hbit
    have hnle : n ≤ j := by
      have := List.mem_range'.1 hj
      omega
    have hlt : σ < 2 ^ j := lt_of_lt_of_le hσ (Nat.pow_le_pow_right (by norm_num) hnle)
    rw [Nat.testBit_eq_false_of_lt hlt] at hbit
    exact Bool.false_ne_true hbit
  rw [htail, mul_one]

private theorem exists_bvec (n : ℕ) (v : Fin n → ZMod 2) :
    ∃ a < 2 ^ n, bvec n a = v := by
  refine ⟨Nat.ofBits fun i => decide (v i = 1), Nat.ofBits_lt_two_pow _, ?_⟩
  funext i
  rw [bvec_apply, Nat.testBit_ofBits_lt _ _ i.2]
  rcases zmod2_cases (v i) with h | h <;> simp [h]

private theorem lD_zero : lD 0 = (1 : Dfull) := by
  rw [lD_eq_prod]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  simp

private theorem tD_zero : tD 0 = (1 : Dfull) := by
  rw [tD_eq, bvec_zero, Psi9]
  rw [show initV (0 : Fin 9 → ZMod 2) = 0 from rfl, Pi.zero_apply, ZMod.val_zero, pow_zero,
    Psi_zero', mul_one]

private theorem exists_tD_of_mem_T9 {t : Dfull} (ht : t ∈ T9) :
    ∃ τ < 2 ^ 9, tD τ = t := by
  let v := Multiplicative.toAdd (tEquiv.symm ⟨t, ht⟩)
  have hv : tEquiv (Multiplicative.ofAdd v) = (⟨t, ht⟩ : T9) := by
    dsimp [v]
    rw [MulEquiv.apply_symm_apply]
  obtain ⟨τ, hτ, hb⟩ := exists_bvec 9 v
  refine ⟨τ, hτ, ?_⟩
  rw [← tOf_eq_tD τ, hb]
  exact congrArg Subtype.val hv

private def N : Subgroup Lgrp := T9.subgroupOf Lgrp

private instance N_normal : N.Normal := Subgroup.normal_of_le_center T9_le_center_Lgrp

private abbrev Q : Type := Lgrp ⧸ N

private def mkQ : Lgrp →* Q := QuotientGroup.mk' N

private def lq (σ : ℕ) : Lgrp := ⟨lD σ, lD_mem_Lgrp σ⟩

private def tq (τ : ℕ) : Lgrp := ⟨tD τ, T9_le_Lgrp (tD_mem_T9 τ)⟩

private def xq (j : ℕ) : Q := mkQ (lq (2 ^ j))

private theorem mkQ_tq (τ : ℕ) : mkQ (tq τ) = 1 := by
  change (tq τ : Q) = 1
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.2 (tD_mem_T9 τ)

private theorem lq_eq_prod (σ : ℕ) :
    lq σ = ((List.range 16).map fun j => if σ.testBit j then lq (2 ^ j) else 1).prod := by
  apply Subtype.ext
  rw [Subgroup.val_list_prod, List.map_map]
  simp only [lq]
  rw [lD_eq_prod]
  congr 1
  apply List.map_congr_left
  intro j hj
  by_cases h : σ.testBit j <;> simp [h]

private theorem mkQ_lq_eq_prod (σ : ℕ) :
    mkQ (lq σ) = ((List.range 16).map fun j => if σ.testBit j then xq j else 1).prod := by
  rw [lq_eq_prod, map_list_prod]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  by_cases h : σ.testBit j <;> simp [xq, h]

private theorem xq_comm {i j : ℕ} (hi : i < 16) (hj : j < 16) :
    xq i * xq j = xq j * xq i := by
  have hrelL : lq (2 ^ i) * lq (2 ^ j) =
      lq (2 ^ j) * lq (2 ^ i) * tq ((lCommN.getD i []).getD j 0) := by
    apply Subtype.ext
    simpa [lq, tq] using lD_mul_lD hi hj
  calc xq i * xq j = mkQ (lq (2 ^ i) * lq (2 ^ j)) := (map_mul mkQ _ _).symm
    _ = mkQ (lq (2 ^ j) * lq (2 ^ i) * tq ((lCommN.getD i []).getD j 0)) := by rw [hrelL]
    _ = mkQ (lq (2 ^ j) * lq (2 ^ i)) * mkQ (tq ((lCommN.getD i []).getD j 0)) := map_mul ..
    _ = mkQ (lq (2 ^ j) * lq (2 ^ i)) := by rw [mkQ_tq, mul_one]
    _ = mkQ (lq (2 ^ j)) * mkQ (lq (2 ^ i)) := map_mul ..
    _ = xq j * xq i := rfl

private theorem mkQ_mem_T9 {t : Dfull} (ht : t ∈ T9) (htL : t ∈ Lgrp) :
    mkQ ⟨t, htL⟩ = 1 := by
  change ((⟨t, htL⟩ : Lgrp) : Q) = 1
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.2 ht

private def genSet : Set Q := {q | ∃ j : ℕ, j < 16 ∧ q = xq j}

private theorem genSet_pairwise : genSet.Pairwise Commute := by
  intro a ha b hb _
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  exact xq_comm hi hj

private theorem mkQ_lq_mem (σ : ℕ) : mkQ (lq σ) ∈ Subgroup.closure genSet := by
  rw [mkQ_lq_eq_prod]
  refine Subgroup.list_prod_mem (Subgroup.closure genSet) fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  by_cases h : σ.testBit j
  · rw [if_pos h]
    exact Subgroup.subset_closure ⟨j, List.mem_range.1 hj, rfl⟩
  · rw [if_neg h]
    exact Subgroup.one_mem _

private theorem wordD_coGens_single_mem (i : ℕ) (hi : i < 9) :
    wordD (coGens.getD i []) ∈ Lgrp := by
  have hmem : coGens.getD i [] ∈ coGens := by
    rw [List.getD_eq_getElem _ _ (by simpa [coGens] using hi)]
    exact List.getElem_mem ..
  exact wordD_mem_Lgrp (coGens_lt _ hmem)
    (rowsCheck_spec rows_check _ (List.mem_append_left _ hmem))

private theorem wordD_pauliWords_single_mem (i : ℕ) (hi : i < 15) :
    wordD (pauliWords.getD i []) ∈ Lgrp := by
  have hmem : pauliWords.getD i [] ∈ pauliWords := by
    rw [List.getD_eq_getElem _ _ (by simpa [pauliWords] using hi)]
    exact List.getElem_mem ..
  exact wordD_mem_Lgrp (fun k hk => by
      have := pauliWords_lt (pauliWords.getD i []) hmem k hk
      omega)
    (rowsCheck_spec rows_check _ (List.mem_append_right _ hmem))

private theorem mkQ_wordD_coGens (i : ℕ) (hi : i < 9) :
    mkQ ⟨wordD (coGens.getD i []), wordD_coGens_single_mem i hi⟩ ∈
      Subgroup.closure genSet := by
  have hL : (⟨wordD (coGens.getD i []), wordD_coGens_single_mem i hi⟩ : Lgrp) =
      lq (coDecN.getD i (0, 0)).1 * tq (coDecN.getD i (0, 0)).2 := by
    apply Subtype.ext
    simpa [lq, tq] using wordD_coGens hi
  rw [hL, map_mul, mkQ_tq, mul_one]
  exact mkQ_lq_mem _

private theorem mkQ_wordD_pauliWords (i : ℕ) (hi : i < 15) :
    mkQ ⟨wordD (pauliWords.getD i []), wordD_pauliWords_single_mem i hi⟩ ∈
      Subgroup.closure genSet := by
  have hL : (⟨wordD (pauliWords.getD i []), wordD_pauliWords_single_mem i hi⟩ : Lgrp) =
      lq (paDecN.getD i (0, 0)).1 * tq (paDecN.getD i (0, 0)).2 := by
    apply Subtype.ext
    simpa [lq, tq] using wordD_pauliWords hi
  rw [hL, map_mul, mkQ_tq, mul_one]
  exact mkQ_lq_mem _

private theorem mkQ_wordD_subWord_mem (gs : List (List ℕ)) (m : ℕ)
    (hL : ∀ i < gs.length, wordD (gs.getD i []) ∈ Lgrp)
    (hC : ∀ i (hi : i < gs.length),
      mkQ ⟨wordD (gs.getD i []), hL i hi⟩ ∈ Subgroup.closure genSet)
    (hsub : wordD (subWord gs m) ∈ Lgrp) :
    mkQ ⟨wordD (subWord gs m), hsub⟩ ∈ Subgroup.closure genSet := by
  classical
  let l := (List.range gs.length).filter fun i => m.testBit i
  let f : ℕ → Lgrp := fun i => if h : i < gs.length then
      ⟨wordD (gs.getD i []), hL i h⟩ else 1
  have hflat : wordD (subWord gs m) = (l.map fun i => wordD (gs.getD i [])).prod := by
    rw [subWord, wordD_flatMap]
  have heq : (⟨wordD (subWord gs m), hsub⟩ : Lgrp) = (l.map f).prod := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod, List.map_map]
    change wordD (subWord gs m) = (l.map (fun i => (f i : Dfull))).prod
    rw [hflat]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hig : i < gs.length := List.mem_range.1 (List.mem_filter.1 hi).1
    dsimp [f]
    rw [dif_pos hig]
  have hEq : mkQ ⟨wordD (subWord gs m), hsub⟩ =
      (l.map (fun i => mkQ (f i))).prod := by
    rw [heq, map_list_prod, List.map_map]
    rfl
  rw [hEq]
  refine Subgroup.list_prod_mem (Subgroup.closure genSet) fun y hy => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
  have hig : i < gs.length := List.mem_range.1 (List.mem_filter.1 hi).1
  dsimp [f]
  rw [dif_pos hig]
  exact hC i hig

private theorem xhat_mem_T9' : xhat ∈ T9 := by
  have h : tD 1 = xhat := by
    simpa [tT] using tD_two_pow (0 : Fin 9)
  rw [← h]
  exact tD_mem_T9 1

private theorem mkQ_wordD_coGens_mem (m : ℕ) :
    mkQ ⟨wordD (subWord coGens m), wordD_coGens_mem_Lgrp rows_check m⟩ ∈
      Subgroup.closure genSet := by
  refine mkQ_wordD_subWord_mem coGens m ?_ ?_ (wordD_coGens_mem_Lgrp rows_check m)
  · intro i hi
    exact wordD_coGens_single_mem i (by simpa [coGens] using hi)
  · intro i hi
    exact mkQ_wordD_coGens i (by simpa [coGens] using hi)

private theorem mkQ_wordD_pauliWords_mem (m : ℕ) :
    mkQ ⟨wordD (subWord pauliWords m), wordD_pauliWords_mem_Lgrp rows_check m⟩ ∈
      Subgroup.closure genSet := by
  refine mkQ_wordD_subWord_mem pauliWords m ?_ ?_ (wordD_pauliWords_mem_Lgrp rows_check m)
  · intro i hi
    exact wordD_pauliWords_single_mem i (by simpa [pauliWords] using hi)
  · intro i hi
    exact mkQ_wordD_pauliWords i (by simpa [pauliWords] using hi)

private theorem closure_genSet_eq_top : Subgroup.closure genSet = ⊤ := by
  refine le_antisymm ?_ ?_
  · exact (Subgroup.closure_le (⊤ : Subgroup Q)).2 fun x _ => Subgroup.mem_top x
  · intro q _
    obtain ⟨x, hxq⟩ := QuotientGroup.mk'_surjective N q
    rw [← hxq]
    change mkQ x ∈ Subgroup.closure genSet
    obtain ⟨m, hm, hproj⟩ := exists_projK_eq rows_check q_check pauli_check x.2
    let w := wordD (subWord coGens m)
    have hwL : w ∈ Lgrp := wordD_coGens_mem_Lgrp rows_check m
    let h := w⁻¹ * (x : Dfull)
    have hhL : h ∈ Lgrp := Lgrp.mul_mem (Lgrp.inv_mem hwL) x.2
    have hhE : h ∈ Ehat := by
      dsimp [h]
      rw [← (projK_eq_one_iff (Amalgam.Lgrp_le_Jhat hhL))]
      rw [projK_mul (Jhat.inv_mem (Amalgam.Lgrp_le_Jhat hwL)) (Amalgam.Lgrp_le_Jhat x.2),
        projK_inv (Amalgam.Lgrp_le_Jhat hwL), hproj]
      exact inv_mul_cancel _
    obtain ⟨m', hm', hψ⟩ := exists_psiD_eq rows_check q_check pauli_check hhL hhE
    let w2 := wordD (subWord pauliWords m')
    have hw2L : w2 ∈ Lgrp := wordD_pauliWords_mem_Lgrp rows_check m'
    have hw2E : w2 ∈ Ehat := (pauliProd_spec m').2.1
    have hψ2 : psiD h = psiD w2 := by
      rw [hψ, ← (pauliProd_spec m').2.2]
    have hxL : xhat ∈ Lgrp := T9_le_Lgrp xhat_mem_T9'
    have hhC : mkQ ⟨h, hhL⟩ ∈ Subgroup.closure genSet := by
      refine (eq_of_psiD_eq hhE hw2E hψ2).elim ?_ ?_
      · intro hw
        rw [show (⟨h, hhL⟩ : Lgrp) = ⟨w2, hw2L⟩ from Subtype.ext hw]
        exact mkQ_wordD_pauliWords_mem m'
      · intro hw
        rw [show (⟨h, hhL⟩ : Lgrp) = ⟨xhat, hxL⟩ * ⟨w2, hw2L⟩ from Subtype.ext hw]
        rw [map_mul, mkQ_mem_T9 xhat_mem_T9' hxL, one_mul]
        exact mkQ_wordD_pauliWords_mem m'
    have hxw : x = (⟨w, hwL⟩ : Lgrp) * ⟨h, hhL⟩ := by
      apply Subtype.ext
      dsimp [h]
      group
    rw [hxw, map_mul]
    exact Subgroup.mul_mem (Subgroup.closure genSet) (mkQ_wordD_coGens_mem m) hhC

private def closureTopEquiv : ↥(Subgroup.closure genSet) ≃* Q where
  toFun x := (x : Q)
  invFun q := ⟨q, by rw [closure_genSet_eq_top]; exact Subgroup.mem_top q⟩
  left_inv x := Subtype.ext rfl
  right_inv q := rfl
  map_mul' x y := rfl

private theorem Q_comm (a b : Q) : a * b = b * a := by
  have : IsMulCommutative ↥(Subgroup.closure genSet) :=
    Subgroup.isMulCommutative_closure genSet_pairwise
  let e := closureTopEquiv
  have h : e.symm a * e.symm b = e.symm b * e.symm a :=
    Std.Commutative.comm (e.symm a) (e.symm b)
  calc a * b = e (e.symm a) * e (e.symm b) := by rw [e.apply_symm_apply, e.apply_symm_apply]
    _ = e (e.symm a * e.symm b) := (map_mul e _ _).symm
    _ = e (e.symm b * e.symm a) := by rw [h]
    _ = e (e.symm b) * e (e.symm a) := map_mul e _ _
    _ = b * a := by rw [e.apply_symm_apply, e.apply_symm_apply]

private theorem list_prod_xor {G : Type*} [CommGroup G] (x : ℕ → G) (n : ℕ)
    (hx : ∀ j < n, x j * x j = 1) (σ σ' : ℕ) :
    (((List.range n).map fun j => if σ.testBit j then x j else 1).prod) *
    (((List.range n).map fun j => if σ'.testBit j then x j else 1).prod) =
    (((List.range n).map fun j => if (σ ^^^ σ').testBit j then x j else 1).prod) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append,
      List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hIH := ih fun j hj => hx j (by omega)
    have hbit : (if σ.testBit n then x n else 1) * (if σ'.testBit n then x n else 1) =
        (if (σ ^^^ σ').testBit n then x n else 1) := by
      rw [Nat.testBit_xor]
      cases hb : σ.testBit n <;> cases hc : σ'.testBit n <;>
        simp [hx n (by omega)]
    rw [mul_mul_mul_comm, hIH, hbit]

private theorem mkQ_lq_mul (σ σ' : ℕ) :
    mkQ (lq σ) * mkQ (lq σ') = mkQ (lq (σ ^^^ σ')) := by
  let : CommGroup Q := CommGroup.mk Q_comm
  rw [mkQ_lq_eq_prod σ, mkQ_lq_eq_prod σ', mkQ_lq_eq_prod (σ ^^^ σ')]
  refine list_prod_xor (fun j => xq j) 16 ?_ σ σ'
  intro j hj
  rw [xq, ← map_mul]
  rw [show lq (2 ^ j) * lq (2 ^ j) = (1 : Lgrp) from by
    apply Subtype.ext
    simpa [lq] using lD_mul_self hj]
  exact map_one mkQ

private theorem lD_mul_lD_mem_T9 (σ σ' : ℕ) :
    lD σ * lD σ' * (lD (σ ^^^ σ'))⁻¹ ∈ T9 := by
  have hQ : mkQ (lq σ * lq σ') = mkQ (lq (σ ^^^ σ')) := by
    rw [map_mul]
    exact mkQ_lq_mul σ σ'
  have hN : (lq σ * lq σ') / lq (σ ^^^ σ') ∈ N :=
    (QuotientGroup.eq_iff_div_mem (N := N)).1 hQ
  rw [div_eq_mul_inv] at hN
  have hT := Subgroup.mem_subgroupOf.1 hN
  simpa [lq, Subgroup.coe_mul, Subgroup.coe_inv] using hT

private theorem lD_mul_lD_eq_mul_tD (σ σ' : ℕ) :
    ∃ τ < 2 ^ 9, lD σ * lD σ' = lD (σ ^^^ σ') * tD τ := by
  obtain ⟨τ, hτ, ht⟩ := exists_tD_of_mem_T9 (lD_mul_lD_mem_T9 σ σ')
  refine ⟨τ, hτ, ?_⟩
  calc lD σ * lD σ' = (lD σ * lD σ' * (lD (σ ^^^ σ'))⁻¹) * lD (σ ^^^ σ') := by group
    _ = tD τ * lD (σ ^^^ σ') := by rw [← ht]
    _ = lD (σ ^^^ σ') * tD τ := (lD_comm_T9 (σ ^^^ σ') (tD_mem_T9 τ)).symm

private theorem mul_normal_form {σ σ' τ τ' : ℕ} (hτ : τ < 2 ^ 9) (hτ' : τ' < 2 ^ 9) :
    ∃ τ'' < 2 ^ 9, (lD σ * tD τ) * (lD σ' * tD τ') = lD (σ ^^^ σ') * tD τ'' := by
  obtain ⟨τ₀, hτ₀, h₀⟩ := lD_mul_lD_eq_mul_tD σ σ'
  refine ⟨τ₀ ^^^ τ ^^^ τ', Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hτ₀ hτ) hτ', ?_⟩
  calc (lD σ * tD τ) * (lD σ' * tD τ')
      = lD σ * (tD τ * lD σ') * tD τ' := by group
    _ = lD σ * (lD σ' * tD τ) * tD τ' := by rw [lD_comm_T9 σ' (tD_mem_T9 τ)]
    _ = (lD σ * lD σ') * tD τ * tD τ' := by group
    _ = (lD (σ ^^^ σ') * tD τ₀) * tD τ * tD τ' := by rw [h₀]
    _ = lD (σ ^^^ σ') * (tD τ₀ * tD τ * tD τ') := by group
    _ = lD (σ ^^^ σ') * (tD (τ₀ ^^^ τ) * tD τ') := by rw [← tD_xor]
    _ = lD (σ ^^^ σ') * tD ((τ₀ ^^^ τ) ^^^ τ') := by rw [← tD_xor]
    _ = lD (σ ^^^ σ') * tD (τ₀ ^^^ τ ^^^ τ') := by congr 1

private def IsNF (g : Dfull) : Prop :=
  ∃ σ < 2 ^ 16, ∃ τ < 2 ^ 9, g = lD σ * tD τ

private theorem isNF_one : IsNF 1 :=
  ⟨0, by norm_num, 0, by norm_num, by rw [lD_zero, tD_zero, mul_one]⟩

private theorem isNF_lD {σ : ℕ} (hσ : σ < 2 ^ 16) : IsNF (lD σ) :=
  ⟨σ, hσ, 0, by norm_num, by rw [tD_zero, mul_one]⟩

private theorem isNF_tD {τ : ℕ} (hτ : τ < 2 ^ 9) : IsNF (tD τ) :=
  ⟨0, by norm_num, τ, hτ, by rw [lD_zero, one_mul]⟩

private theorem isNF_xhat : IsNF xhat := by
  have h : tD 1 = xhat := by
    simpa [tT] using tD_two_pow (0 : Fin 9)
  rw [← h]
  exact isNF_tD (by norm_num)

private theorem IsNF.mul {g h : Dfull} (hg : IsNF g) (hh : IsNF h) : IsNF (g * h) := by
  obtain ⟨σ, hσ, τ, hτ, rfl⟩ := hg
  obtain ⟨σ', hσ', τ', hτ', rfl⟩ := hh
  obtain ⟨τ'', hτ'', h⟩ := mul_normal_form hτ hτ'
  exact ⟨σ ^^^ σ', Nat.xor_lt_two_pow hσ hσ', τ'', hτ'', h⟩

private theorem isNF_list_prod {l : List Dfull} (hl : ∀ x ∈ l, IsNF x) : IsNF l.prod := by
  induction l with
  | nil => simpa using isNF_one
  | cons a l ih =>
    rw [List.prod_cons]
    exact (hl a (List.mem_cons_self ..)).mul
      (ih fun x hx => hl x (List.mem_cons_of_mem _ hx))

private theorem isNF_wordD_subWord {gs : List (List ℕ)}
    (hgs : ∀ i < gs.length, IsNF (wordD (gs.getD i []))) (m : ℕ) :
    IsNF (wordD (subWord gs m)) := by
  rw [subWord, wordD_flatMap]
  refine isNF_list_prod fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact hgs i (List.mem_range.1 (List.mem_filter.1 hi).1)

private theorem coDecN_bounds (i : ℕ) (hi : i < 9) :
    (coDecN.getD i (0, 0)).1 < 2 ^ 16 ∧ (coDecN.getD i (0, 0)).2 < 2 ^ 9 := by
  interval_cases i <;> decide

private theorem paDecN_bounds (i : ℕ) (hi : i < 15) :
    (paDecN.getD i (0, 0)).1 < 2 ^ 16 ∧ (paDecN.getD i (0, 0)).2 < 2 ^ 9 := by
  interval_cases i <;> decide

private theorem isNF_wordD_coGens (i : ℕ) (hi : i < 9) : IsNF (wordD (coGens.getD i [])) := by
  rw [wordD_coGens hi]
  obtain ⟨h1, h2⟩ := coDecN_bounds i hi
  exact (isNF_lD h1).mul (isNF_tD h2)

private theorem isNF_wordD_pauliWords (i : ℕ) (hi : i < 15) :
    IsNF (wordD (pauliWords.getD i [])) := by
  rw [wordD_pauliWords hi]
  obtain ⟨h1, h2⟩ := paDecN_bounds i hi
  exact (isNF_lD h1).mul (isNF_tD h2)

theorem exists_lD_mul_tD {g : Dfull} (hg : g ∈ Lgrp) :
    ∃ σ < 2 ^ 16, ∃ τ < 2 ^ 9, g = lD σ * tD τ := by
  obtain ⟨m, hm, hproj⟩ := exists_projK_eq rows_check q_check pauli_check hg
  let w := wordD (subWord coGens m)
  have hwL : w ∈ Lgrp := wordD_coGens_mem_Lgrp rows_check m
  let h := w⁻¹ * g
  have hhL : h ∈ Lgrp := Lgrp.mul_mem (Lgrp.inv_mem hwL) hg
  have hhE : h ∈ Ehat := by
    dsimp [h]
    rw [← (projK_eq_one_iff (Amalgam.Lgrp_le_Jhat hhL))]
    rw [projK_mul (Jhat.inv_mem (Amalgam.Lgrp_le_Jhat hwL)) (Amalgam.Lgrp_le_Jhat hg),
      projK_inv (Amalgam.Lgrp_le_Jhat hwL), hproj]
    exact inv_mul_cancel _
  obtain ⟨m', hm', hψ⟩ := exists_psiD_eq rows_check q_check pauli_check hhL hhE
  let w2 := wordD (subWord pauliWords m')
  have hw2E : w2 ∈ Ehat := (pauliProd_spec m').2.1
  have hψ2 : psiD h = psiD w2 := by
    rw [hψ, ← (pauliProd_spec m').2.2]
  have hwNF : IsNF w :=
    isNF_wordD_subWord (gs := coGens)
      (fun i hi => isNF_wordD_coGens i (by simpa [coGens] using hi)) m
  have hhNF : IsNF h := by
    refine (eq_of_psiD_eq hhE hw2E hψ2).elim ?_ ?_
    · intro hw
      rw [hw]
      exact isNF_wordD_subWord (gs := pauliWords)
        (fun i hi => isNF_wordD_pauliWords i (by simpa [pauliWords] using hi)) m'
    · intro hw
      rw [hw]
      exact isNF_xhat.mul (isNF_wordD_subWord (gs := pauliWords)
        (fun i hi => isNF_wordD_pauliWords i (by simpa [pauliWords] using hi)) m')
  have hg_eq : g = w * h := by
    dsimp [h]
    group
  rw [hg_eq]
  exact hwNF.mul hhNF

private def phiNF : Fin (2 ^ 16) × Fin (2 ^ 9) → Lgrp := fun p =>
  ⟨lD (p.1 : ℕ) * tD (p.2 : ℕ),
    Lgrp.mul_mem (lD_mem_Lgrp _) (T9_le_Lgrp (tD_mem_T9 _))⟩

private theorem phiNF_surjective : Function.Surjective phiNF := by
  intro g
  obtain ⟨σ, hσ, τ, hτ, hg⟩ := exists_lD_mul_tD g.2
  refine ⟨(⟨σ, hσ⟩, ⟨τ, hτ⟩), ?_⟩
  apply Subtype.ext
  exact hg.symm

private theorem card_phiNF_domain :
    Nat.card (Fin (2 ^ 16) × Fin (2 ^ 9)) = 2 ^ 25 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin (2 ^ 16)),
    Nat.card_eq_fintype_card (α := Fin (2 ^ 9)), Fintype.card_fin, Fintype.card_fin]
  norm_num

private theorem phiNF_bijective : Function.Bijective phiNF :=
  phiNF_surjective.bijective_of_nat_card_le (by rw [card_phiNF_domain, ← natCard_Lgrp])

theorem lD_mul_tD_inj {σ σ' τ τ' : ℕ} (hσ : σ < 2 ^ 16) (hσ' : σ' < 2 ^ 16) (hτ : τ < 2 ^ 9)
    (hτ' : τ' < 2 ^ 9) (h : lD σ * tD τ = lD σ' * tD τ') : σ = σ' ∧ τ = τ' := by
  let a : Fin (2 ^ 16) × Fin (2 ^ 9) := (⟨σ, hσ⟩, ⟨τ, hτ⟩)
  let b : Fin (2 ^ 16) × Fin (2 ^ 9) := (⟨σ', hσ'⟩, ⟨τ', hτ'⟩)
  have hphi : phiNF a = phiNF b := by
    apply Subtype.ext
    simpa [phiNF, a, b] using h
  have hp := phiNF_bijective.1 hphi
  have h1 : σ = σ' := by
    simpa [a, b] using congrArg (fun p : Fin (2 ^ 16) × Fin (2 ^ 9) => (p.1 : ℕ)) hp
  have h2 : τ = τ' := by
    simpa [a, b] using congrArg (fun p : Fin (2 ^ 16) × Fin (2 ^ 9) => (p.2 : ℕ)) hp
  exact ⟨h1, h2⟩

private noncomputable def sCoordNat (g : Lgrp) : ℕ :=
  Classical.choose (exists_lD_mul_tD g.2)

private theorem sCoordNat_spec (g : Lgrp) :
    sCoordNat g < 2 ^ 16 ∧ ∃ τ < 2 ^ 9, (g : Dfull) = lD (sCoordNat g) * tD τ :=
  Classical.choose_spec (exists_lD_mul_tD g.2)

private noncomputable def sCoordTau (g : Lgrp) : ℕ :=
  Classical.choose (sCoordNat_spec g).2

private theorem sCoordTau_spec (g : Lgrp) :
    sCoordTau g < 2 ^ 9 ∧ (g : Dfull) = lD (sCoordNat g) * tD (sCoordTau g) :=
  Classical.choose_spec (sCoordNat_spec g).2

private theorem lD_eq_one_of_bvec_zero {σ : ℕ} (h : bvec 16 σ = 0) : lD σ = 1 := by
  rw [lD_eq_prod]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have hb : σ.testBit j = false := by
    have h1 := congrFun h ⟨j, List.mem_range.1 hj⟩
    rw [bvec_apply] at h1
    cases hbit : σ.testBit j
    · rfl
    · exfalso
      rw [if_pos hbit] at h1
      exact one_ne_zero h1
  simp [hb]

def sCoord : Lgrp →* Multiplicative (Fin 16 → ZMod 2) where
  toFun g := Multiplicative.ofAdd (bvec 16 (sCoordNat g))
  map_one' := by
    have h0 : lD 0 * tD 0 = (1 : Dfull) := by rw [lD_zero, tD_zero, mul_one]
    have hdec : lD (sCoordNat 1) * tD (sCoordTau 1) = lD 0 * tD 0 := by
      rw [← (sCoordTau_spec 1).2, h0, Subgroup.coe_one]
    have huniq := lD_mul_tD_inj (sCoordNat_spec 1).1 (by norm_num)
      (sCoordTau_spec 1).1 (by norm_num) hdec
    rw [huniq.1]
    rw [bvec_zero, ofAdd_zero]
  map_mul' g h := by
    obtain ⟨τ'', hτ'', hmul⟩ := mul_normal_form (sCoordTau_spec g).1 (sCoordTau_spec h).1
    have hgh : ((g * h : Lgrp) : Dfull) = lD (sCoordNat g ^^^ sCoordNat h) * tD τ'' := by
      rw [Subgroup.coe_mul, (sCoordTau_spec g).2, (sCoordTau_spec h).2]
      exact hmul
    have hdec : lD (sCoordNat (g * h)) * tD (sCoordTau (g * h)) =
        lD (sCoordNat g ^^^ sCoordNat h) * tD τ'' := by
      rw [← (sCoordTau_spec (g * h)).2, hgh]
    have huniq := lD_mul_tD_inj (sCoordNat_spec (g * h)).1
      (Nat.xor_lt_two_pow (sCoordNat_spec g).1 (sCoordNat_spec h).1)
      (sCoordTau_spec (g * h)).1 hτ'' hdec
    rw [huniq.1, bvec_xor]
    exact ofAdd_add _ _

theorem sCoord_lD_mul {σ : ℕ} (hσ : σ < 2 ^ 16) {t : Dfull} (ht : t ∈ T9)
    (h : lD σ * t ∈ Lgrp) : sCoord ⟨lD σ * t, h⟩ = Multiplicative.ofAdd (bvec 16 σ) := by
  obtain ⟨τ, hτ, htτ⟩ := exists_tD_of_mem_T9 ht
  have hg : ((⟨lD σ * t, h⟩ : Lgrp) : Dfull) = lD σ * tD τ := by
    simp [htτ]
  have hdec : lD (sCoordNat ⟨lD σ * t, h⟩) * tD (sCoordTau ⟨lD σ * t, h⟩) =
      lD σ * tD τ := by
    rw [← (sCoordTau_spec ⟨lD σ * t, h⟩).2, hg]
  have huniq := lD_mul_tD_inj (sCoordNat_spec ⟨lD σ * t, h⟩).1 hσ
    (sCoordTau_spec ⟨lD σ * t, h⟩).1 hτ hdec
  change Multiplicative.ofAdd (bvec 16 (sCoordNat ⟨lD σ * t, h⟩)) =
    Multiplicative.ofAdd (bvec 16 σ)
  rw [huniq.1]

theorem sCoord_eq_one_iff (g : Lgrp) : sCoord g = 1 ↔ (g : Dfull) ∈ T9 := by
  constructor
  · intro hg
    have ht := (sCoordTau_spec g).2
    have hb : bvec 16 (sCoordNat g) = 0 := by
      have h1 : Multiplicative.toAdd (sCoord g) = 0 := by
        rw [hg, toAdd_one]
      simpa [sCoord] using h1
    have hl : lD (sCoordNat g) = 1 := lD_eq_one_of_bvec_zero hb
    rw [ht, hl, one_mul]
    exact tD_mem_T9 (sCoordTau g)
  · intro hg
    obtain ⟨τ, hτ, ht⟩ := exists_tD_of_mem_T9 hg
    have hdec : lD (sCoordNat g) * tD (sCoordTau g) = lD 0 * tD τ := by
      rw [← (sCoordTau_spec g).2, lD_zero, one_mul, ← ht]
    have huniq := lD_mul_tD_inj (sCoordNat_spec g).1 (by norm_num)
      (sCoordTau_spec g).1 hτ hdec
    change Multiplicative.ofAdd (bvec 16 (sCoordNat g)) = 1
    rw [huniq.1, bvec_zero, ofAdd_zero]

theorem sCoord_surjective : Function.Surjective sCoord := by
  intro v
  obtain ⟨σ, hσ, hb⟩ := exists_bvec 16 (Multiplicative.toAdd v)
  refine ⟨⟨lD σ, lD_mem_Lgrp σ⟩, ?_⟩
  have heq : (⟨lD σ * 1, Lgrp.mul_mem (lD_mem_Lgrp σ) Lgrp.one_mem⟩ : Lgrp) =
      ⟨lD σ, lD_mem_Lgrp σ⟩ := Subtype.ext (mul_one _)
  rw [← heq, sCoord_lD_mul hσ T9.one_mem, hb, ofAdd_toAdd]

theorem commutator_mem_T9 (x y : Lgrp) : ⁅(x : Dfull), (y : Dfull)⁆ ∈ T9 := by
  have hmem : ⁅(x : Dfull), (y : Dfull)⁆ ∈ Lgrp := by
    rw [commutatorElement_def]
    exact Lgrp.mul_mem (Lgrp.mul_mem (Lgrp.mul_mem x.2 y.2) (Lgrp.inv_mem x.2))
      (Lgrp.inv_mem y.2)
  change ((⟨⁅(x : Dfull), (y : Dfull)⁆, hmem⟩ : Lgrp) : Dfull) ∈ T9
  rw [← sCoord_eq_one_iff]
  have hmap : sCoord ⟨⁅(x : Dfull), (y : Dfull)⁆, hmem⟩ = ⁅sCoord x, sCoord y⁆ := by
    change sCoord ((⟨(x : Dfull), x.2⟩ : Lgrp) * ⟨(y : Dfull), y.2⟩ *
      (⟨(x : Dfull), x.2⟩ : Lgrp)⁻¹ * (⟨(y : Dfull), y.2⟩ : Lgrp)⁻¹) =
      sCoord x * sCoord y * (sCoord x)⁻¹ * (sCoord y)⁻¹
    simp only [map_mul, map_inv]
  have hcomm : ⁅sCoord x, sCoord y⁆ = 1 := by
    rw [commutatorElement_def]
    simp
  rw [hmap, hcomm]

private theorem mul_comm_of_mem_T9 {a t : Dfull} (ha : a ∈ Lgrp) (ht : t ∈ T9) :
    a * t = t * a := by
  have hmem : (⟨t, T9_le_Lgrp ht⟩ : Lgrp) ∈ T9.subgroupOf Lgrp :=
    Subgroup.mem_subgroupOf.2 ht
  have h := Subgroup.mem_center_iff.1 (T9_le_center_Lgrp hmem) ⟨a, ha⟩
  exact congrArg Subtype.val h

private theorem commutator_mul_left {a b y : Dfull}
    (ha : a ∈ Lgrp) (_hb : b ∈ Lgrp) (_hy : y ∈ Lgrp)
    (hby : ⁅b, y⁆ ∈ T9) (_hay : ⁅a, y⁆ ∈ T9) :
    ⁅a * b, y⁆ = ⁅b, y⁆ * ⁅a, y⁆ := by
  have h1 : b * y * b⁻¹ = ⁅b, y⁆ * y := by
    rw [commutatorElement_def]
    group
  rw [commutatorElement_def, mul_inv_rev]
  calc a * b * y * (b⁻¹ * a⁻¹) * y⁻¹
      = a * (b * y * b⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = a * (⁅b, y⁆ * y) * a⁻¹ * y⁻¹ := by rw [h1]
    _ = (a * ⁅b, y⁆) * y * a⁻¹ * y⁻¹ := by group
    _ = (⁅b, y⁆ * a) * y * a⁻¹ * y⁻¹ := by
        rw [mul_comm_of_mem_T9 ha hby]
    _ = ⁅b, y⁆ * (a * y * a⁻¹ * y⁻¹) := by group
    _ = ⁅b, y⁆ * ⁅a, y⁆ := by
        rw [show a * y * a⁻¹ * y⁻¹ = ⁅a, y⁆ from by rw [commutatorElement_def]]

private theorem commutator_mul_right {x a b : Dfull}
    (_hx : x ∈ Lgrp) (ha : a ∈ Lgrp) (_hb : b ∈ Lgrp)
    (_hxa : ⁅x, a⁆ ∈ T9) (hxb : ⁅x, b⁆ ∈ T9) :
    ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
  rw [commutatorElement_def, mul_inv_rev]
  calc x * (a * b) * x⁻¹ * (b⁻¹ * a⁻¹)
      = (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    _ = ⁅x, a⁆ * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by
        rw [show x * a * x⁻¹ * a⁻¹ = ⁅x, a⁆ from by rw [commutatorElement_def]]
    _ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
        rw [show x * b * x⁻¹ * b⁻¹ = ⁅x, b⁆ from by rw [commutatorElement_def]]
    _ = ⁅x, a⁆ * ⁅x, b⁆ := by
        rw [show a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ from by
          rw [mul_comm_of_mem_T9 ha hxb]
          group]

private theorem list_prod_mem_Lgrp {l : List Dfull} (hl : ∀ x ∈ l, x ∈ Lgrp) : l.prod ∈ Lgrp :=
  Subgroup.list_prod_mem Lgrp hl

private theorem commutator_list_prod_left (l : List Dfull) (y : Dfull)
    (hl : ∀ x ∈ l, x ∈ Lgrp) (hy : y ∈ Lgrp) :
    ⁅l.prod, y⁆ = (l.map fun x => ⁅x, y⁆).prod := by
  induction l with
  | nil => simp [commutatorElement_def]
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    have haL : a ∈ Lgrp := hl a (List.mem_cons_self ..)
    have hlL : ∀ x ∈ l, x ∈ Lgrp := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hbL : l.prod ∈ Lgrp := list_prod_mem_Lgrp hlL
    have hT : ⁅l.prod, y⁆ ∈ T9 := by
      have hh := commutator_mem_T9 ⟨l.prod, hbL⟩ ⟨y, hy⟩
      simpa using hh
    have haT : ⁅a, y⁆ ∈ T9 := by
      have hh := commutator_mem_T9 ⟨a, haL⟩ ⟨y, hy⟩
      simpa using hh
    rw [commutator_mul_left haL hbL hy hT haT]
    rw [ih hlL]
    have h2T : (l.map fun x => ⁅x, y⁆).prod ∈ T9 := by
      apply Subgroup.list_prod_mem T9
      intro z hz
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hz
      have hh := commutator_mem_T9 ⟨v, hlL v hv⟩ ⟨y, hy⟩
      simpa using hh
    rw [T9_mul_comm h2T haT]

private theorem commutator_list_prod_right (x : Dfull) (l : List Dfull)
    (hx : x ∈ Lgrp) (hl : ∀ y ∈ l, y ∈ Lgrp) :
    ⁅x, l.prod⁆ = (l.map fun y => ⁅x, y⁆).prod := by
  induction l with
  | nil => simp [commutatorElement_def]
  | cons b l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    have hbL : b ∈ Lgrp := hl b (List.mem_cons_self ..)
    have hlL : ∀ y ∈ l, y ∈ Lgrp := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hbT : ⁅x, b⁆ ∈ T9 := by
      have hh := commutator_mem_T9 ⟨x, hx⟩ ⟨b, hbL⟩
      simpa using hh
    have hlT : ⁅x, l.prod⁆ ∈ T9 := by
      have hh := commutator_mem_T9 ⟨x, hx⟩ ⟨l.prod, list_prod_mem_Lgrp hlL⟩
      simpa using hh
    rw [commutator_mul_right hx hbL (list_prod_mem_Lgrp hlL) hbT hlT]
    rw [ih hlL]

private theorem comm_gen {i j : ℕ} (hi : i < 16) (hj : j < 16) :
    ⁅lD (2 ^ i), lD (2 ^ j)⁆ = tD ((lCommN.getD i []).getD j 0) := by
  set a := lD (2 ^ i)
  set b := lD (2 ^ j)
  set c := tD ((lCommN.getD i []).getD j 0)
  have ha : a * a = 1 := lD_mul_self hi
  have hb : b * b = 1 := lD_mul_self hj
  have hc : c ∈ T9 := tD_mem_T9 _
  have hca : a * c = c * a := mul_comm_of_mem_T9 (lD_mem_Lgrp (2 ^ i)) hc
  have hcb : b * c = c * b := mul_comm_of_mem_T9 (lD_mem_Lgrp (2 ^ j)) hc
  have hrel : a * b = b * a * c := lD_mul_lD hi hj
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
  calc a * b * a * b = (b * a * c) * a * b := by rw [hrel]
    _ = b * (a * c) * a * b := by group
    _ = b * (c * a) * a * b := by rw [hca]
    _ = b * c * (a * a) * b := by group
    _ = b * c * b := by rw [ha, mul_one]
    _ = c * b * b := by rw [hcb]
    _ = c := by rw [mul_assoc, hb, mul_one]

private theorem commutator_list_prod_list (l1 l2 : List Dfull)
    (hl1 : ∀ x ∈ l1, x ∈ Lgrp) (hl2 : ∀ y ∈ l2, y ∈ Lgrp) :
    ⁅l1.prod, l2.prod⁆ =
      (l1.flatMap fun x => l2.map fun y => ⁅x, y⁆).prod := by
  rw [commutator_list_prod_left l1 l2.prod hl1 (list_prod_mem_Lgrp hl2)]
  induction l1 with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.flatMap_cons, List.prod_append]
    rw [commutator_list_prod_right a l2 (hl1 a (List.mem_cons_self ..)) hl2]
    rw [ih fun x hx => hl1 x (List.mem_cons_of_mem _ hx)]

private theorem list_sum_flatMap {α : Type*} (l : List α) (f : α → List (Fin 9 → ZMod 2)) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

private theorem list_sum_range_eq_finset_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = (Finset.range n).sum f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private def lDlist (σ : ℕ) : List Dfull :=
  (List.range 16).map fun j => if σ.testBit j then lD (2 ^ j) else 1

private theorem lDlist_prod (σ : ℕ) : (lDlist σ).prod = lD σ :=
  (lD_eq_prod σ).symm

private theorem lDlist_mem (σ : ℕ) : ∀ x ∈ lDlist σ, x ∈ Lgrp := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  by_cases h : σ.testBit j
  · simp [h, lD_mem_Lgrp]
  · simp [h]

private theorem commutator_mul_T9_left {x t y : Dfull}
    (_hx : x ∈ Lgrp) (ht : t ∈ T9) (hy : y ∈ Lgrp) :
    ⁅x * t, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, mul_inv_rev]
  have hcomm : t * y = y * t := (mul_comm_of_mem_T9 hy ht).symm
  calc x * t * y * (t⁻¹ * x⁻¹) * y⁻¹
      = x * (t * y) * (t⁻¹ * x⁻¹) * y⁻¹ := by group
    _ = x * (y * t) * (t⁻¹ * x⁻¹) * y⁻¹ := by rw [hcomm]
    _ = x * y * x⁻¹ * y⁻¹ := by group
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]

private theorem commutator_mul_T9_right {x y t : Dfull}
    (hx : x ∈ Lgrp) (hy : y ∈ Lgrp) (ht : t ∈ T9) :
    ⁅x, y * t⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, mul_inv_rev]
  have hyt : y * t = t * y := mul_comm_of_mem_T9 hy ht
  have hxt : x * t = t * x := mul_comm_of_mem_T9 hx ht
  have hxc : x * y * x⁻¹ ∈ Lgrp :=
    Lgrp.mul_mem (Lgrp.mul_mem hx hy) (Lgrp.inv_mem hx)
  have hct : t * (x * y * x⁻¹) = (x * y * x⁻¹) * t :=
    (mul_comm_of_mem_T9 hxc ht).symm
  calc x * (y * t) * x⁻¹ * (t⁻¹ * y⁻¹)
      = x * (t * y) * x⁻¹ * (t⁻¹ * y⁻¹) := by rw [hyt]
    _ = (x * t) * y * x⁻¹ * (t⁻¹ * y⁻¹) := by group
    _ = (t * x) * y * x⁻¹ * (t⁻¹ * y⁻¹) := by rw [hxt]
    _ = t * (x * y * x⁻¹) * t⁻¹ * y⁻¹ := by group
    _ = (x * y * x⁻¹) * t * t⁻¹ * y⁻¹ := by rw [hct]
    _ = x * y * x⁻¹ * y⁻¹ := by group
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]

private theorem tVec_comm_one_right (x : Dfull) : tVec ⁅x, 1⁆ = 0 := by
  rw [commutatorElement_def]
  simp [tVec_one]

private theorem tVec_comm_one_left (y : Dfull) : tVec ⁅(1 : Dfull), y⁆ = 0 := by
  rw [commutatorElement_def]
  simp [tVec_one]

private theorem map_lDlist {α : Type*} (F : Dfull → α) (σ : ℕ) :
    (lDlist σ).map F = (List.range 16).map fun i =>
      F (if σ.testBit i then lD (2 ^ i) else 1) := by
  rw [lDlist, List.map_map]
  rfl

private theorem inner_sum_lD (i : ℕ) (hi : i < 16) (σ' : ℕ) :
    ((lDlist σ').map fun y => tVec ⁅lD (2 ^ i), y⁆).sum =
    (Finset.range 16).sum fun j =>
      if σ'.testBit j then bvec 9 ((lCommN.getD i []).getD j 0) else 0 := by
  rw [lDlist, List.map_map]
  rw [list_sum_range_eq_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hj16 : j < 16 := Finset.mem_range.1 hj
  by_cases h : σ'.testBit j
  · simp only [Function.comp_apply, h, if_true]
    rw [comm_gen hi hj16, tVec_tD]
  · simp only [Function.comp_apply, if_neg h]
    rw [tVec_comm_one_right]

private theorem list_sum_map_zero {α : Type*} (l : List α) :
    (l.map fun _ => (0 : Fin 9 → ZMod 2)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l _ih => simp

private theorem outer_sum_lD (σ σ' : ℕ) :
    ((lDlist σ).map fun x => ((lDlist σ').map fun y => tVec ⁅x, y⁆).sum).sum =
    (Finset.range 16).sum fun i =>
      if σ.testBit i then
        (Finset.range 16).sum fun j =>
          if σ'.testBit j then bvec 9 ((lCommN.getD i []).getD j 0) else 0
      else 0 := by
  rw [map_lDlist]
  rw [list_sum_range_eq_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi16 : i < 16 := Finset.mem_range.1 hi
  by_cases h : σ.testBit i
  · simp only [h, if_true]
    exact inner_sum_lD i hi16 σ'
  · simp only [if_neg h]
    rw [show (lDlist σ').map (fun y => tVec ⁅(1 : Dfull), y⁆) =
        (lDlist σ').map (fun _ => (0 : Fin 9 → ZMod 2)) from by
      apply List.map_congr_left
      intro y hy
      exact tVec_comm_one_left y]
    exact list_sum_map_zero _

private theorem finset_double_sum_eq_lBeta (σ σ' : ℕ) :
    (Finset.range 16).sum (fun i =>
      if σ.testBit i then
        (Finset.range 16).sum (fun j =>
          if σ'.testBit j then bvec 9 ((lCommN.getD i []).getD j 0) else 0)
      else 0) =
    lBeta (bvec 16 σ) (bvec 16 σ') := by
  rw [lBeta, Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi16 : i < 16 := Finset.mem_range.1 hi
  simp only [dif_pos hi16]
  by_cases hi : σ.testBit i
  · simp only [hi, if_true]
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj16 : j < 16 := Finset.mem_range.1 hj
    simp only [dif_pos hj16]
    rw [bvec_apply, bvec_apply]
    by_cases h2 : σ'.testBit j <;> simp [hi, h2]
  · simp only [hi]
    rw [Finset.sum_fin_eq_sum_range]
    symm
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj16 : j < 16 := Finset.mem_range.1 hj
    simp only [dif_pos hj16]
    rw [bvec_apply]
    simp [hi]

private theorem tVec_commutator_lD (σ σ' : ℕ) :
    tVec ⁅lD σ, lD σ'⁆ = lBeta (bvec 16 σ) (bvec 16 σ') := by
  rw [lD_eq_prod σ, lD_eq_prod σ']
  change tVec ⁅(lDlist σ).prod, (lDlist σ').prod⁆ =
    lBeta (bvec 16 σ) (bvec 16 σ')
  rw [commutator_list_prod_list (lDlist σ) (lDlist σ') (lDlist_mem σ) (lDlist_mem σ')]
  have hmem : ∀ x ∈ (lDlist σ).flatMap
      (fun x => (lDlist σ').map fun y => ⁅x, y⁆), x ∈ T9 := by
    intro x hx
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.1 hx
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    have hh := commutator_mem_T9 ⟨a, lDlist_mem σ a ha⟩ ⟨b', lDlist_mem σ' b' hb'⟩
    simpa using hh
  rw [tVec_list_prod hmem]
  rw [List.map_flatMap]
  simp only [List.map_map, Function.comp_def]
  rw [list_sum_flatMap]
  rw [outer_sum_lD]
  exact finset_double_sum_eq_lBeta σ σ'

theorem tVec_commutator (x y : Lgrp) :
    tVec ⁅(x : Dfull), (y : Dfull)⁆ = lBeta (sCoord x).toAdd (sCoord y).toAdd := by
  obtain ⟨σ, hσ, τ, hτ, hx⟩ := exists_lD_mul_tD x.2
  obtain ⟨σ', hσ', τ', hτ', hy⟩ := exists_lD_mul_tD y.2
  have hxL : lD σ * tD τ ∈ Lgrp := by rw [← hx]; exact x.2
  have hyL : lD σ' * tD τ' ∈ Lgrp := by rw [← hy]; exact y.2
  have hx' : x = (⟨lD σ * tD τ, hxL⟩ : Lgrp) := Subtype.ext hx
  have hy' : y = (⟨lD σ' * tD τ', hyL⟩ : Lgrp) := Subtype.ext hy
  have hcoordx : (sCoord x).toAdd = bvec 16 σ := by
    rw [hx', sCoord_lD_mul hσ (tD_mem_T9 τ) hxL]
    exact toAdd_ofAdd _
  have hcoordy : (sCoord y).toAdd = bvec 16 σ' := by
    rw [hy', sCoord_lD_mul hσ' (tD_mem_T9 τ') hyL]
    exact toAdd_ofAdd _
  have hcomm : ⁅(x : Dfull), (y : Dfull)⁆ = ⁅lD σ, lD σ'⁆ := by
    rw [hx, hy]
    rw [commutator_mul_T9_right
      (Lgrp.mul_mem (lD_mem_Lgrp σ) (T9_le_Lgrp (tD_mem_T9 τ)))
      (lD_mem_Lgrp σ') (tD_mem_T9 τ')]
    rw [commutator_mul_T9_left (lD_mem_Lgrp σ) (tD_mem_T9 τ) (lD_mem_Lgrp σ')]
  rw [hcomm, hcoordx, hcoordy]
  exact tVec_commutator_lD σ σ'

theorem sq_mem_T9 (x : Lgrp) : (x : Dfull) ^ 2 ∈ T9 := by
  have hmem : (x : Dfull) ^ 2 ∈ Lgrp := Lgrp.pow_mem x.2 2
  change ((⟨(x : Dfull) ^ 2, hmem⟩ : Lgrp) : Dfull) ∈ T9
  rw [← sCoord_eq_one_iff]
  have hmap : sCoord ⟨(x : Dfull) ^ 2, hmem⟩ = (sCoord x) ^ 2 := by
    have hp : (⟨(x : Dfull) ^ 2, hmem⟩ : Lgrp) = (⟨(x : Dfull), x.2⟩ : Lgrp) ^ 2 :=
      Subtype.ext (Subgroup.coe_pow Lgrp ⟨(x : Dfull), x.2⟩ 2).symm
    rw [hp, map_pow]
  have hsq : (sCoord x) ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    exact ZModModule.add_self _
  rw [hmap, hsq]

private def lDprefix (σ n : ℕ) : Dfull :=
  ((List.range n).map fun j => if σ.testBit j then lD (2 ^ j) else 1).prod

private theorem lDprefix_mem (σ n : ℕ) :
    ∀ x ∈ ((List.range n).map fun j => if σ.testBit j then lD (2 ^ j) else 1), x ∈ Lgrp := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  by_cases h : σ.testBit j
  · simp [h, lD_mem_Lgrp]
  · simp [h]

private theorem lDprefix_prod_mem (σ n : ℕ) : lDprefix σ n ∈ Lgrp :=
  list_prod_mem_Lgrp (lDprefix_mem σ n)

private theorem lDprefix_succ (σ n : ℕ) :
    lDprefix σ (n + 1) = lDprefix σ n * (if σ.testBit n then lD (2 ^ n) else 1) := by
  unfold lDprefix
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

private theorem lDprefix_sixteen (σ : ℕ) : lDprefix σ 16 = lD σ := by
  unfold lDprefix
  rw [lD_eq_prod]

private theorem sq_mul_involution {w c : Dfull}
    (hw : w ∈ Lgrp) (hc : c ∈ Lgrp) (hc2 : c * c = 1) :
    (w * c) * (w * c) = (w * w) * ⁅c, w⁆ := by
  have hcomm : ⁅c, w⁆ ∈ T9 := by
    have hh := commutator_mem_T9 ⟨c, hc⟩ ⟨w, hw⟩
    simpa using hh
  have hcw : c * w = ⁅c, w⁆ * (w * c) := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hc2]
    rw [show (c * w * c * w⁻¹) * (w * c) = c * w * (c * c) from by group]
    rw [hc2, mul_one]
  calc (w * c) * (w * c) = w * (c * w) * c := by group
    _ = w * (⁅c, w⁆ * (w * c)) * c := by rw [hcw]
    _ = w * ⁅c, w⁆ * (w * (c * c)) := by group
    _ = w * ⁅c, w⁆ * w := by rw [hc2, mul_one]
    _ = (w * w) * ⁅c, w⁆ := by
        rw [mul_comm_of_mem_T9 hw hcomm, mul_assoc,
          mul_comm_of_mem_T9 (Lgrp.mul_mem hw hw) hcomm]

private theorem tVec_comm_prefix (σ n : ℕ) (hn : n < 16) :
    tVec ⁅(if σ.testBit n then lD (2 ^ n) else 1), lDprefix σ n⁆ =
      if σ.testBit n then
        (Finset.range n).sum fun j =>
          if σ.testBit j then bvec 9 ((lCommN.getD n []).getD j 0) else 0
      else 0 := by
  let c := if σ.testBit n then lD (2 ^ n) else 1
  let l := (List.range n).map fun j => if σ.testBit j then lD (2 ^ j) else 1
  have hw : lDprefix σ n = l.prod := rfl
  have hc : c ∈ Lgrp := by
    dsimp [c]
    by_cases h : σ.testBit n <;> simp [h, lD_mem_Lgrp]
  have hl : ∀ x ∈ l, x ∈ Lgrp := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    by_cases h : σ.testBit j <;> simp [h, lD_mem_Lgrp]
  change tVec ⁅c, lDprefix σ n⁆ =
    if σ.testBit n then
      (Finset.range n).sum fun j =>
        if σ.testBit j then bvec 9 ((lCommN.getD n []).getD j 0) else 0
    else 0
  rw [hw, commutator_list_prod_right c l hc hl]
  have hmem : ∀ x ∈ l.map (fun y => ⁅c, y⁆), x ∈ T9 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hh := commutator_mem_T9 ⟨c, hc⟩ ⟨y, hl y hy⟩
    simpa using hh
  rw [tVec_list_prod hmem]
  by_cases hbit : σ.testBit n
  · simp only [hbit, if_true]
    have hcL : c = lD (2 ^ n) := by simp [c, hbit]
    rw [hcL]
    rw [show l = (List.range n).map
        (fun j => if σ.testBit j then lD (2 ^ j) else 1) from rfl]
    simp only [List.map_map]
    rw [list_sum_range_eq_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjlt : j < n := Finset.mem_range.1 hj
    have hj16 : j < 16 := lt_trans hjlt hn
    by_cases hb : σ.testBit j
    · simp only [Function.comp_apply, hb, if_true]
      rw [comm_gen hn hj16, tVec_tD]
    · simp only [Function.comp_apply, if_neg hb]
      rw [tVec_comm_one_right]
  · simp only [hbit, if_false, Bool.false_eq_true]
    have hc1 : c = 1 := by simp [c, hbit]
    rw [hc1]
    rw [List.map_map]
    change (l.map (fun y => tVec ⁅(1 : Dfull), y⁆)).sum = 0
    rw [show l.map (fun y => tVec ⁅(1 : Dfull), y⁆) =
        l.map (fun _ => (0 : Fin 9 → ZMod 2)) from by
      apply List.map_congr_left
      intro y hy
      exact tVec_comm_one_left y]
    exact list_sum_map_zero _

private theorem tVec_sq_prefix (σ : ℕ) :
    ∀ n ≤ 16, tVec ((lDprefix σ n) ^ 2) =
      (Finset.range n).sum fun i =>
        if σ.testBit i then
          (Finset.range i).sum fun j =>
            if σ.testBit j then bvec 9 ((lCommN.getD i []).getD j 0) else 0
        else 0 := by
  intro n
  refine Nat.le_induction (m := 0) ?base ?step n (Nat.zero_le n)
  · intro hn
    simp [lDprefix, tVec_one]
  · intro n hmn ih hn1
    have hn : n < 16 := Nat.lt_of_succ_le hn1
    have ih' := ih (le_of_lt hn)
    let w := lDprefix σ n
    let c := if σ.testBit n then lD (2 ^ n) else 1
    have hrec : lDprefix σ (n + 1) = w * c := by
      simpa [w, c] using lDprefix_succ σ n
    rw [hrec]
    have hw : w ∈ Lgrp := lDprefix_prod_mem σ n
    have hc : c ∈ Lgrp := by
      dsimp [c]
      by_cases h : σ.testBit n <;> simp [h, lD_mem_Lgrp]
    have hc2 : c * c = 1 := by
      dsimp [c]
      by_cases h : σ.testBit n
      · simp [h, lD_mul_self hn]
      · simp [h]
    have hw2 : w * w ∈ T9 := by
      have hh := sq_mem_T9 ⟨w, hw⟩
      simpa [pow_two] using hh
    have hcomm : ⁅c, w⁆ ∈ T9 := by
      have hh := commutator_mem_T9 ⟨c, hc⟩ ⟨w, hw⟩
      simpa using hh
    have hsq : (w * c) * (w * c) = (w * w) * ⁅c, w⁆ :=
      sq_mul_involution hw hc hc2
    rw [show (w * c) ^ 2 = (w * c) * (w * c) from by rw [pow_two]]
    rw [hsq, tVec_mul hw2 hcomm]
    rw [show tVec (w * w) = (Finset.range n).sum fun i =>
        if σ.testBit i then
          (Finset.range i).sum fun j =>
            if σ.testBit j then bvec 9 ((lCommN.getD i []).getD j 0) else 0
        else 0 from by
      simpa [w, pow_two] using ih']
    rw [tVec_comm_prefix σ n hn]
    rw [Finset.sum_range_succ]

private theorem sum_range_ite_lt {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) {n j : ℕ} (hj : j ≤ n) :
    (Finset.range n).sum (fun i => if i < j then f i else 0) =
      (Finset.range j).sum f := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hi⟩
    exact hi
  · intro hi
    exact ⟨lt_of_lt_of_le hi hj, hi⟩

private theorem sum_fin_ite_lt {M : Type*} [AddCommMonoid M]
    (j : Fin 16) (f : Fin 16 → M) :
    (∑ i : Fin 16, if i < j then f i else 0) =
      (Finset.range (j : ℕ)).sum fun i => if h : i < 16 then f ⟨i, h⟩ else 0 := by
  rw [Finset.sum_fin_eq_sum_range]
  rw [show (Finset.range 16).sum (fun i => if hi : i < 16 then
      (if (⟨i, hi⟩ : Fin 16) < j then f ⟨i, hi⟩ else 0) else 0) =
    (Finset.range 16).sum (fun i => if i < (j : ℕ) then
      (if hi : i < 16 then f ⟨i, hi⟩ else 0) else 0) from by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hi16 : i < 16
    · have hlt : (⟨i, hi16⟩ : Fin 16) < j ↔ i < (j : ℕ) := by
        rw [Fin.lt_def]
      by_cases hij : i < (j : ℕ)
      · simp [hi16, hlt, hij]
      · have hnot : ¬ (⟨i, hi16⟩ : Fin 16) < j := by simpa [hlt] using hij
        simp [hi16, hij, hnot]
    · have hnot : ¬ i < (j : ℕ) := fun h => hi16 (lt_trans h j.2)
      simp [hi16, hnot]]
  rw [← sum_range_ite_lt (fun i => if h : i < 16 then f ⟨i, h⟩ else 0) (le_of_lt j.2)]

private theorem lQuad_eq_qsum (σ : ℕ) :
    lQuad (bvec 16 σ) =
      (Finset.range 16).sum fun i =>
        if σ.testBit i then
          (Finset.range i).sum fun j =>
            if σ.testBit j then bvec 9 ((lCommN.getD i []).getD j 0) else 0
        else 0 := by
  rw [lQuad, Finset.sum_comm]
  nth_rewrite 1 [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hj16 : j < 16 := Finset.mem_range.1 hj
  simp only [dif_pos hj16]
  rw [sum_fin_ite_lt ⟨j, hj16⟩ (fun i => (bvec 16 σ i * bvec 16 σ ⟨j, hj16⟩) •
    bvec 9 ((lCommN.getD j []).getD i 0))]
  by_cases hbit : σ.testBit j
  · simp only [hbit, if_true]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi16 : i < 16 := lt_trans (Finset.mem_range.1 hi) hj16
    simp only [dif_pos hi16]
    rw [bvec_apply, bvec_apply]
    by_cases hibit : σ.testBit i <;> simp [hbit, hibit]
  · simp only [hbit]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi16 : i < 16 := lt_trans (Finset.mem_range.1 hi) hj16
    simp only [dif_pos hi16]
    simp only [bvec_apply]
    simp [hbit]

theorem tVec_sq (x : Lgrp) : tVec ((x : Dfull) ^ 2) = lQuad (sCoord x).toAdd := by
  obtain ⟨σ, hσ, τ, hτ, hx⟩ := exists_lD_mul_tD x.2
  have hxL : lD σ * tD τ ∈ Lgrp := by rw [← hx]; exact x.2
  have hcoord : (sCoord x).toAdd = bvec 16 σ := by
    have hx' : x = (⟨lD σ * tD τ, hxL⟩ : Lgrp) := Subtype.ext hx
    rw [hx', sCoord_lD_mul hσ (tD_mem_T9 τ) hxL]
    exact toAdd_ofAdd _
  have ht2 : tD τ * tD τ = 1 := by
    rw [← tD_xor, Nat.xor_self, tD_zero]
  have hsq : (x : Dfull) ^ 2 = (lD σ) ^ 2 := by
    rw [hx, pow_two]
    have hcomm : lD σ * tD τ = tD τ * lD σ := lD_comm_T9 σ (tD_mem_T9 τ)
    calc (lD σ * tD τ) * (lD σ * tD τ)
        = lD σ * (tD τ * lD σ) * tD τ := by group
      _ = lD σ * (lD σ * tD τ) * tD τ := by rw [hcomm]
      _ = (lD σ * lD σ) * (tD τ * tD τ) := by group
      _ = (lD σ * lD σ) * 1 := by rw [ht2]
      _ = lD σ * lD σ := by rw [mul_one]
    rw [pow_two]
  rw [hcoord, hsq, ← lDprefix_sixteen σ]
  rw [tVec_sq_prefix σ 16 (by norm_num), ← lQuad_eq_qsum]

end CFSG.Monster.B.TwoA.Sp8.WordRel

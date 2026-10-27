
module

public import CFSG.Monster.B.TwoA.Sp8.WordRel
public import CFSG.Monster.B.TwoA.Sp8.P0StructInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoDFix

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

private theorem flatMap_range_two_pow {α : Type*} (n j : ℕ) (hj : j < n)
    (f : ℕ → List α) :
    (List.range n).flatMap (fun i => if (2 ^ j).testBit i then f i else []) = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | heq
    · rw [ih hlt]
      have h1 : (2 ^ j).testBit n = false :=
        Nat.testBit_lt_two_pow (Nat.pow_lt_pow_right (by decide) hlt)
      simp [h1]
    · subst heq
      rw [List.flatMap_eq_nil_iff.mpr ?_, List.nil_append, List.flatMap_singleton,
        Nat.testBit_two_pow_self, if_pos rfl]
      intro i hi
      rw [List.mem_range] at hi
      rw [Nat.testBit_two_pow, if_neg]
      simp [Ne.symm (Nat.ne_of_lt hi)]

private theorem tWord_two_pow (j : ℕ) (hj : j < 9) :
    tWord (2 ^ j) = [tLetters.getD j (.lift 0)] :=
  flatMap_range_two_pow 9 j hj (fun j => [tLetters.getD j (.lift 0)])

private theorem tWord_eq_finRange (τ : ℕ) :
    tWord τ = (List.finRange 9).flatMap (fun j : Fin 9 =>
      if τ.testBit (j : ℕ) then [tLetters.getD (j : ℕ) (.lift 0)] else []) := by
  rw [tWord, ← List.map_coe_finRange_eq_range (n := 9), List.flatMap_map]

private theorem tLetters_getD_lt7 (j : Fin 8) (hj : (j : ℕ) < 7) :
    tLetters.getD (j : ℕ) (.lift 0) = .pc (liftP j) := by
  fin_cases j <;> first | rfl | exact absurd hj (by decide)

private theorem lWord_two_pow (j : ℕ) (hj : j < 16) :
    lWord (2 ^ j) = (lGenWords.getD j []).map XLetter.lift :=
  flatMap_range_two_pow 16 j hj (fun i => (lGenWords.getD i []).map XLetter.lift)

private theorem lGenWords_lt : ∀ j < 16, ∀ k ∈ lGenWords.getD j [], k < 44 := by
  intro j hj
  interval_cases j <;> simp [lGenWords]

private theorem lGenWords_mem : ∀ j < 16, lGenWords.getD j [] ∈ coGens ++ pauliWords := by
  intro j hj
  interval_cases j <;> simp [lGenWords, coGens, pauliWords]

private theorem uGenWords_lt (k : ℕ) (hk : k < 10) :
    ∀ j ∈ uGenWords.getD k [], j < 44 := by
  interval_cases k <;> simp [uGenWords]

private theorem uGenWords_fixed (k : ℕ) (hk : k < 10) :
    actWord (uGenWords.getD k []) 1 = 1 ∧
    actWord (uGenWords.getD k []) 2 = 2 ∧
    actWord (uGenWords.getD k []) 12 = 12 ∧
    actWord (uGenWords.getD k []) 48 = 48 := by
  interval_cases k <;> decide

@[expose] def lam0 : Submodule (ZMod 2) V8 :=
  Submodule.span (ZMod 2) {bvec 8 1, bvec 8 2, bvec 8 12, bvec 8 48}

private theorem b0_gen_zero :
    ∀ g ∈ [bvec 8 1, bvec 8 2, bvec 8 12, bvec 8 48],
      ∀ y ∈ [bvec 8 1, bvec 8 2, bvec 8 12, bvec 8 48], b0 g y = 0 := by
  decide +kernel

theorem lam0_isotropic : IsTotallyIsotropic b0 lam0 := by
  intro x hx y hy
  have hgen : ∀ g ∈ ({bvec 8 1, bvec 8 2, bvec 8 12, bvec 8 48} : Set V8),
      ∀ y ∈ lam0, b0 g y = 0 := by
    intro g hg y hy'
    refine Submodule.span_induction (p := fun y _ => b0 g y = 0) ?_ ?_ ?_ ?_ hy'
    · intro y hy''
      have hmem : g ∈ [bvec 8 1, bvec 8 2, bvec 8 12, bvec 8 48] := by
        simpa using hg
      have hmem' : y ∈ [bvec 8 1, bvec 8 2, bvec 8 12, bvec 8 48] := by
        simpa using hy''
      exact b0_gen_zero g hmem y hmem'
    · simp
    · intro y z hy1 hz1 ihy ihz
      rw [map_add, ihy, ihz, add_zero]
    · intro c y hy1 ih
      rw [map_smul, ih, smul_zero]
  refine Submodule.span_induction (p := fun x _ => b0 x y = 0) ?_ ?_ ?_ ?_ hx
  · intro x hx'
    exact hgen x hx' y hy
  · simp
  · intro x z hx1 hz1 ihx ihz
    rw [map_add, LinearMap.add_apply, ihx, ihz, add_zero]
  · intro c x hx1 ih
    rw [map_smul, LinearMap.smul_apply, ih, smul_zero]

private theorem linind_lam0 :
    LinearIndependent (ZMod 2) ![bvec 8 1, bvec 8 2, bvec 8 12, bvec 8 48] := by
  refine (Fintype.linearIndependent_iff).2 ?_
  decide +kernel

theorem finrank_lam0 : Module.finrank (ZMod 2) lam0 = 4 := by
  have hLI := linind_lam0
  have h := finrank_span_eq_card hLI
  have hset : (Set.range ![bvec 8 1, bvec 8 2, bvec 8 12, bvec 8 48]) =
      ({bvec 8 1, bvec 8 2, bvec 8 12, bvec 8 48} : Set V8) := by
    ext x
    simp [or_comm, or_left_comm]
  rw [hset] at h
  rw [show lam0 = Submodule.span (ZMod 2) {bvec 8 1, bvec 8 2, bvec 8 12, bvec 8 48} from rfl]
  exact h

theorem e0_mem_lam0 : e0 ∈ lam0 := by
  have h : e0 = bvec 8 1 := by
    funext i
    fin_cases i <;> simp [e0, bvec] <;> decide
  rw [h]
  exact Submodule.subset_span (by simp)

section

@[expose] def lD (σ : ℕ) : Dfull := wordX (lWord σ)

@[expose] def tD (τ : ℕ) : Dfull := wordX (tWord τ)

@[expose] def uD (k : ℕ) : Dfull := wordX (uWord k)

private theorem wordX_lWord (σ : ℕ) : wordX (lWord σ) = lD σ := rfl

private theorem wordX_tWord (τ : ℕ) : wordX (tWord τ) = tD τ := rfl

private theorem wordX_uWord (k : ℕ) : wordX (uWord k) = uD k := rfl

private theorem wordX_flatMap {α : Type*} (l : List α) (f : α → List XLetter) :
    wordX (l.flatMap f) = (l.map (fun j => wordX (f j))).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, wordX_append, ih, List.map_cons, List.prod_cons]

private theorem wordX_flatMap_range (n : ℕ) (f : ℕ → List XLetter) :
    wordX ((List.range n).flatMap f) = ((List.range n).map (fun j => wordX (f j))).prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, wordX_append, ih, List.map_append, List.prod_append,
      List.flatMap_singleton, List.map_singleton, List.prod_singleton]

private theorem lD_two_pow (j : ℕ) (hj : j < 16) :
    lD (2 ^ j) = wordD (lGenWords.getD j []) := by
  rw [lD, lWord_two_pow j hj, wordX_map_lift]

theorem lD_eq_prod (σ : ℕ) :
    lD σ = ((List.range 16).map fun j => if σ.testBit j then lD (2 ^ j) else 1).prod := by
  rw [lD, lWord, wordX_flatMap_range]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  by_cases h : σ.testBit j
  · rw [if_pos h, if_pos h, lD_two_pow j hj, wordX_map_lift]
  · rw [if_neg h, if_neg h, wordX_nil]

private theorem uD_eq_wordD (k : ℕ) : uD k = wordD (uGenWords.getD k []) := by
  rw [uD, uWord, wordX_map_lift]

end

private theorem Psi9_zero :
    Psi9 (0 : Fin 9 → ZMod 2) = 1 := by
  rw [Psi9]
  have h : initV (0 : Fin 9 → ZMod 2) = 0 := rfl
  rw [h, Psi_zero', Pi.zero_apply, ZMod.val_zero, pow_zero, mul_one]

private theorem Psi9_smul_single
    (j : Fin 9) (z : ZMod 2) :
    Psi9 (z • Pi.single j 1) = if z = 1 then tT j else 1 := by
  rcases zmod2_cases z with rfl | rfl
  · simp [Psi9_zero]
  · simp [Psi9_single]

private theorem Psi9_sum_list
    (τ : ℕ) (l : List (Fin 9)) :
    Psi9 ((l.map (fun (j : Fin 9) => bvec 9 τ j • Pi.single j 1)).sum) =
      (l.map (fun (j : Fin 9) => if τ.testBit (j : ℕ) then tT j else 1)).prod := by
  induction l with
  | nil => simp [Psi9_zero]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, Psi9_add, ih, List.map_cons, List.prod_cons,
      Psi9_smul_single]
    by_cases h : τ.testBit (a : ℕ) <;> simp [bvec, h]

private theorem Psi9_eq_prod
    (τ : ℕ) :
    Psi9 (bvec 9 τ) = ((List.finRange 9).map (fun j : Fin 9 =>
      if τ.testBit (j : ℕ) then tT j else 1)).prod := by
  have hv : bvec 9 τ =
      ((List.finRange 9).map (fun (j : Fin 9) => bvec 9 τ j • Pi.single j 1)).sum := by
    calc bvec 9 τ = ∑ j : Fin 9, Pi.single j (bvec 9 τ j) := (Finset.univ_sum_single _).symm
      _ = ∑ j : Fin 9, bvec 9 τ j • (Pi.single j 1 : Fin 9 → ZMod 2) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      _ = ((List.finRange 9).map (fun (j : Fin 9) => bvec 9 τ j • Pi.single j 1)).sum := rfl
  rw [hv]
  exact Psi9_sum_list τ (List.finRange 9)

private theorem tD_two_pow_castSucc (j : Fin 8) :
    tD (2 ^ (j : ℕ)) = aT j := by
  rw [tD, tWord_two_pow (j : ℕ) (by omega), wordX_cons, wordX_nil, mul_one]
  by_cases hj : (j : ℕ) < 7
  · rw [tLetters_getD_lt7 j hj, toD_pc, ← foldP_checks.2.1 j,
      ← PhiD_eq_pcD (Pi.single j 1), PhiD_single hj]
  · have h7 : j = 7 := Fin.ext (by omega)
    subst h7
    change (tLetters.getD 7 (.lift 0)).toD = aT 7
    rw [show tLetters.getD 7 (.lift 0) = .sign 3 from rfl, toD_sign_three, aT_seven]

theorem tD_two_pow (j : Fin 9) : tD (2 ^ (j : ℕ)) = tT j := by
  refine Fin.lastCases ?_ (fun j8 => ?_) j
  · change tD (2 ^ (8 : ℕ)) = cQ
    rw [tD, tWord_two_pow 8 (by decide), wordX_cons, wordX_nil, mul_one]
    rw [show tLetters.getD 8 (.lift 0) = .pc cPauli from rfl, toD_pc, ← cQ_eq_pcD]
  · rw [tT_castSucc j8]
    exact tD_two_pow_castSucc j8

private theorem tD_eq_prod (τ : ℕ) :
    tD τ = ((List.finRange 9).map (fun j : Fin 9 =>
      if τ.testBit (j : ℕ) then tT j else 1)).prod := by
  rw [tD, tWord_eq_finRange, wordX_flatMap]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  by_cases h : τ.testBit (j : ℕ)
  · rw [if_pos h, if_pos h]
    rw [← tWord_two_pow (j : ℕ) (by omega)]
    exact tD_two_pow j
  · rw [if_neg h, if_neg h, wordX_nil]

theorem tD_eq (τ : ℕ) : tD τ = Psi9 (bvec 9 τ) := by
  rw [tD_eq_prod, Psi9_eq_prod]

theorem tD_mem_T9 (τ : ℕ) : tD τ ∈ T9 := by
  rw [tD_eq]
  exact Psi9_mem_T9 _

theorem tD_xor (τ τ' : ℕ) : tD (τ ^^^ τ') = tD τ * tD τ' := by
  rw [tD_eq, tD_eq, tD_eq, bvec_xor, Psi9_add]

private theorem lD_two_pow_mem_Lgrp (j : ℕ) (hj : j < 16) :
    lD (2 ^ j) ∈ Lgrp := by
  rw [lD_two_pow j hj]
  exact wordD_mem_Lgrp (lGenWords_lt j hj)
    (rowsCheck_spec rows_check _ (lGenWords_mem j hj))

theorem lD_mem_Lgrp (σ : ℕ) : lD σ ∈ Lgrp := by
  rw [lD_eq_prod]
  apply list_prod_mem
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  rw [List.mem_range] at hj
  by_cases h : σ.testBit j
  · rw [if_pos h]
    exact lD_two_pow_mem_Lgrp j hj
  · rw [if_neg h]
    exact Lgrp.one_mem

end CFSG.Monster.B.TwoA.Sp8.WordRel

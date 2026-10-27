module

public import CFSG.RankThree.GF2n.Parrott.SpinFixedS

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a1A" => (⟨alpha1, alpha1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b1A" => (⟨beta1, beta1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : A45)

private theorem ncard_le_length_of_bitmask {P : V → Prop} (L : List ℕ)
    (hL : ∀ v, P v → bitmask v ∈ L) : {v : V | P v}.ncard ≤ L.length := by
  have hsub : {v : V | P v} ⊆ ((L.toFinset.image vecOfNat : Finset V) : Set V) := by
    intro v hv
    have h1 := hL v hv
    have h2 : bitmask v < 256 := bitmask_lt v
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    refine ⟨bitmask v, h1, ?_⟩
    apply bitmask_injective
    exact bitmask_vecOfNat _ h2
  calc {v : V | P v}.ncard ≤ ((L.toFinset.image vecOfNat : Finset V) : Set V).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (L.toFinset.image vecOfNat).card := Set.ncard_coe_finset _
    _ ≤ L.toFinset.card := Finset.card_image_le
    _ ≤ L.length := List.toFinset_card_le L

private theorem fix_uv_al_check : ∀ m < 256,
    bapply (bmul (evalB b3 (toW lU)) (bmul (b3 0) (b3 2))) m = m →
      bapply (evalB b3 (toW lAl)) m = m → m ∈ [0, 26, 64, 90] := by
  decide +kernel

private theorem fix_v_u_t_check : ∀ m < 256,
    (bapply (bmul (b3 0) (b3 2)) m = m ∧ bapply (evalB b3 (toW lU)) m = m ∧
      bapply (evalB b3 (toW lT)) m = m) → m ∈ [0, 26, 64, 90] := by
  decide +kernel

private def sWord (k : ℕ) : List (Fin 3 × ℕ) :=
  (if k % 2 = 1 then toW lU else []) ++ (if k / 2 % 2 = 1 then toW lAl else []) ++
    (if k / 4 % 2 = 1 then toW lBe else []) ++ (if k / 8 % 2 = 1 then toW lT else [])

private def nWords : List (List (Fin 3 × ℕ)) :=
  [[(1, 1), (2, 1), (1, 4), (1, 4)], [(1, 1), (1, 1), (2, 1), (1, 4)],
    [(1, 1), (1, 1), (2, 1), (1, 1), (2, 1), (1, 4)],
    [(1, 4), (0, 1), (2, 1), (1, 1), (1, 1), (0, 1), (1, 1)],
    [(1, 4), (2, 1), (1, 4), (0, 1), (2, 1), (1, 1), (1, 1)]]

private def rWords : List (List (Fin 3 × ℕ)) :=
  [toW lU, toW lAl, toW lBe, toW lT, toW lU ++ toW lT]

private def conjCodes : List (List ℕ) :=
  [[13, 9, 10, 15, 2], [15, 9, 3, 13, 2], [8, 2, 6, 1, 9], [8, 14, 10, 13, 5], [11, 5, 2, 1, 10]]

private theorem conj_codes_ok : ∀ i < 5, ∀ j < 5,
    tcomp (evalT t3 (nWords.getD i [])) (evalT t3 (rWords.getD j [])) =
      tcomp (evalT t3 (sWord ((conjCodes.getD i []).getD j 0))) (evalT t3 (nWords.getD i [])) := by
  decide +kernel

private def genChecks : List (List (Fin 3 × ℕ) × ℕ × ℕ × ℕ × ℕ) :=
  [(toW lU, 1, 0, 0, 0), (toW lAl, 15, 13, 0, 0), (toW lBe, 8, 13, 1, 0), (toW lT, 8, 0, 0, 0),
    (toW lU, 9, 2, 10, 0), (toW lAl, 2, 0, 0, 0), (toW lBe, 9, 2, 5, 10), (toW lT, 2, 10, 0, 0)]

private theorem genChecks_ok : ∀ e ∈ genChecks,
    tcomp (evalT t3 e.1) (evalT t3 []) =
      tcomp (evalT t3 (sWord e.2.1 ++ sWord e.2.2.1))
        (evalT t3 (sWord e.2.2.2.1 ++ sWord e.2.2.2.2)) := by
  decide +kernel

private def c1m : ℕ := 10

private def c2m : ℕ := 33

private def cosetIdx (m : ℕ) : ℕ :=
  if fixesS m = true then 0 else if fixesS (m ^^^ c1m) = true then 1
    else if fixesS (m ^^^ c2m) = true then 2 else 3

private def compMask (k : ℕ) : ℕ :=
  (if k % 2 = 1 then c1m else 0) ^^^ (if k / 2 = 1 then c2m else 0)

private def epsOf (e1 e2 : ZMod 2) (m : ℕ) : ZMod 2 :=
  (if cosetIdx m % 2 = 1 then e1 else 0) + (if cosetIdx m / 2 = 1 then e2 else 0)

private def aWord : Fin 3 → List (Fin 3 × ℕ)
  | 0 => []
  | 1 => [(1, 4), (0, 1), (1, 4)]
  | 2 => [(1, 1), (0, 1), (1, 4), (1, 4)]

private def aCode : Fin 3 → ℕ
  | 0 => 8
  | 1 => 13
  | 2 => 13

private theorem cosetIdx_lt (m : ℕ) : cosetIdx m < 4 := by
  unfold cosetIdx
  split_ifs <;> omega

private theorem coset_check : ∀ m < 256, fixesT m = true →
    fixesS (m ^^^ compMask (cosetIdx m)) = true := by
  decide +kernel

private theorem c1m_fixesT : fixesT c1m = true := by decide +kernel

private theorem c2m_fixesT : fixesT c2m = true := by decide +kernel

private theorem c1m_lt : c1m < 256 := by decide

private theorem c2m_lt : c2m < 256 := by decide

private theorem aCode_ok : ∀ i : Fin 3,
    tcomp (evalT t3 (toW lT)) (evalT t3 (aWord i)) =
      tcomp (evalT t3 (aWord i)) (evalT t3 (sWord (aCode i))) := by
  decide +kernel

private def wMasks : List ℕ :=
  [0, 4, 26, 30, 64, 68, 90, 94, 128, 132, 154, 158, 192, 196, 218, 222]

private theorem fixesS_iff_mem_wMasks : ∀ m < 256, fixesS m = true ↔ m ∈ wMasks := by
  decide +kernel

private theorem cover_check : ∀ e1 e2 : ZMod 2, ∀ m < 256, fixesT m = true →
    ((qTab.getD m 0 : ℕ) : ZMod 2) = epsOf e1 e2 m →
    ∃ i : Fin 3, ∀ w ∈ wMasks,
      epsOf e1 e2 (bapply (evalB b3 (aWord i)) w) =
        ((bq m (bapply (evalB b3 (aWord i)) w) : ℕ) : ZMod 2) := by
  decide +kernel

private abbrev wordElt (w : List (Fin 3 × ℕ)) : A45 := evalSpinWord spinGenA w

private theorem eq_of_word_tcomp {w₁ w₂ w₃ w₄ : List (Fin 3 × ℕ)}
    (h : tcomp (evalT t3 w₁) (evalT t3 w₂) = tcomp (evalT t3 w₃) (evalT t3 w₄)) :
    wordElt w₁ * wordElt w₂ = wordElt w₃ * wordElt w₄ := by
  apply eq_of_permTab_eq
  have e : (fun i => permTab ((spinGenA i : A45) : Equiv.Perm (Fin 45))) = t3 :=
    funext permTab_spinGenA
  rw [permTab_coe_mul, permTab_coe_mul, permTab_coe_evalSpinWord, permTab_coe_evalSpinWord,
    permTab_coe_evalSpinWord, permTab_coe_evalSpinWord, e]
  exact h

private theorem wordElt_append (w₁ w₂ : List (Fin 3 × ℕ)) :
    wordElt (w₁ ++ w₂) = wordElt w₁ * wordElt w₂ := by
  simp [wordElt, evalSpinWord, List.map_append, List.prod_append]

private theorem wordElt_nil : wordElt [] = 1 := rfl

private theorem ite_wordElt (c : Prop) [Decidable c] {g : A45} {w : List (Fin 3 × ℕ)}
    (h : g = wordElt w) : (if c then g else 1) = wordElt (if c then w else []) := by
  split_ifs
  · exact h
  · rfl

private theorem v_add_self (x : V) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private theorem q_eq_cast (v : V) : q v = ((qTab.getD (bitmask v) 0 : ℕ) : ZMod 2) := by
  rw [← q_val_eq_qTab, ZMod.natCast_zmod_val]

private theorem b_eq_cast (v w : V) : b v w = ((bq (bitmask v) (bitmask w) : ℕ) : ZMod 2) := by
  have h : (b v w).val = bq (bitmask v) (bitmask w) := by
    unfold b bq
    rw [ZMod.val_add, ZMod.val_add, q_val_eq_qTab, q_val_eq_qTab, q_val_eq_qTab, bitmask_add]
    omega
  rw [← h, ZMod.natCast_zmod_val]

private def compV (k : ℕ) : V :=
  (if k % 2 = 1 then vecOfNat c1m else 0) + (if k / 2 = 1 then vecOfNat c2m else 0)

private theorem bitmask_compV (k : ℕ) : bitmask (compV k) = compMask k := by
  unfold compV compMask
  rw [bitmask_add]
  congr 1
  · split_ifs
    · exact bitmask_vecOfNat _ c1m_lt
    · exact bitmask_zero
  · split_ifs
    · exact bitmask_vecOfNat _ c2m_lt
    · exact bitmask_zero

section FixedVectors


private theorem ncard_fix_le_of_conj {X E : Subgroup A45} {g : A45}
    (h : X.map (MulAut.conj g).toMonoidHom = E) :
    {v : V | ∀ s ∈ X, SpinFixes s v}.ncard ≤ {v : V | ∀ s ∈ E, SpinFixes s v}.ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun v => ((rhoA g : GL8) : Mat8) *ᵥ v) ?_ ?_
    (Set.toFinite _)
  · intro v hv s hs
    rw [← h] at hs
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hs
    apply spinFixes_mulVec_of_conj
    have h1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    show SpinFixes (g⁻¹ * (g * x * g⁻¹) * g) v
    rw [h1]
    exact hv x hx
  · intro v _ w _ hvw
    have h1 := congrArg (fun z => ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ z) hvw
    simpa only [rhoA_mulVec_inv] using h1

private theorem vA_eq : vA = spinGenA 0 * spinGenA 2 := by
  apply Subtype.ext
  show v = x45 * f45
  decide +kernel

private theorem cols_vA : colsOf (spinMat vA) = bmul (b3 0) (b3 2) := by
  rw [vA_eq, map_mul, colsOf_mul, spinMat_spinGenA, spinMat_spinGenA]

private theorem ncard_fix_eUV_le : {v : V | ∀ s ∈ eUVQA45, SpinFixes s v}.ncard ≤ 4 := by
  have h := ncard_le_length_of_bitmask (P := fun v : V => ∀ s ∈ eUVQA45, SpinFixes s v)
    [0, 26, 64, 90] (fun v hv => by
      have h1 : SpinFixes (uA * vA) v := hv _ (Subgroup.subset_closure (Set.mem_insert _ _))
      have h2 : SpinFixes (a1A * a2A) v := hv _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      rw [spinFixes_iff, map_mul, colsOf_mul, cols_uA, cols_vA] at h1
      rw [spinFixes_iff, cols_alA] at h2
      exact fix_uv_al_check _ (bitmask_lt v) h1 h2)
  exact h

private theorem ncard_fix_eV_le : {v : V | ∀ s ∈ eVQA45, SpinFixes s v}.ncard ≤ 4 := by
  have h := ncard_le_length_of_bitmask (P := fun v : V => ∀ s ∈ eVQA45, SpinFixes s v)
    [0, 26, 64, 90] (fun v hv => by
      have h1 : SpinFixes vA v := hv _ (Subgroup.subset_closure (Set.mem_insert _ _))
      have h2 : SpinFixes uA v := hv _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      have h3 : SpinFixes tA v := hv _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
      rw [spinFixes_iff, cols_vA] at h1
      rw [spinFixes_iff, cols_uA] at h2
      rw [spinFixes_iff, cols_tA] at h3
      exact fix_v_u_t_check _ (bitmask_lt v) ⟨h1, h2, h3⟩)
  exact h

section Fixed16


theorem qa45SubgroupConj_sQA45_of_fixed (X : Subgroup A45) (hX : IsElemAbelian 2 X)
    (hc : Nat.card X = 16) (hfix : 16 ≤ Set.ncard {v : V | ∀ s ∈ X, SpinFixes s v}) :
    QA45SubgroupConj X sQA45 := by
  rcases (qa45_elemAbelian_sixteen).1 X hX hc with h | h | h
  · exact h
  · obtain ⟨g, hg⟩ := h
    have h1 := (ncard_fix_le_of_conj hg).trans ncard_fix_eUV_le
    omega
  · obtain ⟨g, hg⟩ := h
    have h1 := (ncard_fix_le_of_conj hg).trans ncard_fix_eV_le
    omega

end Fixed16

end FixedVectors

section Normalizer


private def sElt (k : ℕ) : A45 :=
  (if k % 2 = 1 then uA else 1) * (if k / 2 % 2 = 1 then a1A * a2A else 1) *
    (if k / 4 % 2 = 1 then b1A * b2A else 1) * (if k / 8 % 2 = 1 then tA else 1)

private theorem sElt_mem (k : ℕ) : sElt k ∈ sQA45 := by
  have h1 : (if k % 2 = 1 then uA else 1) ∈ sQA45 := by
    split_ifs
    · exact uA_mem_S
    · exact one_mem _
  have h2 : (if k / 2 % 2 = 1 then a1A * a2A else 1) ∈ sQA45 := by
    split_ifs
    · exact alA_mem_S
    · exact one_mem _
  have h3 : (if k / 4 % 2 = 1 then b1A * b2A else 1) ∈ sQA45 := by
    split_ifs
    · exact beA_mem_S
    · exact one_mem _
  have h4 : (if k / 8 % 2 = 1 then tA else 1) ∈ sQA45 := by
    split_ifs
    · exact tA_mem_S
    · exact one_mem _
  exact mul_mem (mul_mem (mul_mem h1 h2) h3) h4

private theorem sElt_eq_word (k : ℕ) : sElt k = wordElt (sWord k) := by
  unfold sElt sWord
  rw [wordElt_append, wordElt_append, wordElt_append, ← ite_wordElt _ uA_eq,
    ← ite_wordElt _ alA_eq, ← ite_wordElt _ beA_eq, ← ite_wordElt _ tA_eq]

private theorem conj_code_elt (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    wordElt (nWords.getD i []) * wordElt (rWords.getD j []) =
      sElt ((conjCodes.getD i []).getD j 0) * wordElt (nWords.getD i []) := by
  rw [sElt_eq_word]
  exact eq_of_word_tcomp (conj_codes_ok i hi j hj)

private theorem conj_mem_S (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    wordElt (nWords.getD i []) * wordElt (rWords.getD j []) * (wordElt (nWords.getD i []))⁻¹ ∈
      sQA45 := by
  rw [mul_inv_eq_iff_eq_mul.2 (conj_code_elt i j hi hj)]
  exact sElt_mem _

private theorem wordElt_mem_normalizer (i : ℕ) (hi : i < 5) :
    wordElt (nWords.getD i []) ∈ Subgroup.normalizer (sQA45 : Set A45) := by
  show _ ∈ Subgroup.normalizer ((Subgroup.closure {uA, a1A * a2A, b1A * b2A, tA} :
    Subgroup A45) : Set A45)
  refine CFSG.GroupTheory.mem_normalizer_closure fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have h := conj_mem_S i 0 hi (by norm_num)
    change wordElt (nWords.getD i []) * wordElt (toW lU) * _ ∈ sQA45 at h
    have e : wordElt (toW lU) = uA := uA_eq.symm
    rw [e] at h
    exact h
  · have h := conj_mem_S i 1 hi (by norm_num)
    change wordElt (nWords.getD i []) * wordElt (toW lAl) * _ ∈ sQA45 at h
    have e : wordElt (toW lAl) = a1A * a2A := alA_eq.symm
    rw [e] at h
    exact h
  · have h := conj_mem_S i 2 hi (by norm_num)
    change wordElt (nWords.getD i []) * wordElt (toW lBe) * _ ∈ sQA45 at h
    have e : wordElt (toW lBe) = b1A * b2A := beA_eq.symm
    rw [e] at h
    exact h
  · have h := conj_mem_S i 3 hi (by norm_num)
    change wordElt (nWords.getD i []) * wordElt (toW lT) * _ ∈ sQA45 at h
    have e : wordElt (toW lT) = tA := tA_eq.symm
    rw [e] at h
    exact h

private theorem gen_eq_prod {e : List (Fin 3 × ℕ) × ℕ × ℕ × ℕ × ℕ} (he : e ∈ genChecks) {g : A45}
    (hg : g = wordElt e.1) :
    g = (sElt e.2.1 * sElt e.2.2.1) * (sElt e.2.2.2.1 * sElt e.2.2.2.2) := by
  have h := eq_of_word_tcomp (w₁ := e.1) (w₂ := []) (w₃ := sWord e.2.1 ++ sWord e.2.2.1)
    (w₄ := sWord e.2.2.2.1 ++ sWord e.2.2.2.2) (genChecks_ok e he)
  rw [wordElt_append, wordElt_append, wordElt_nil, mul_one, ← sElt_eq_word, ← sElt_eq_word,
    ← sElt_eq_word, ← sElt_eq_word] at h
  rw [hg]
  exact h

private theorem sElt_zero : sElt 0 = 1 := by
  simp [sElt]

private theorem sQA45_le_of_gens {K : Subgroup A45} (hu : uA ∈ K) (hal : a1A * a2A ∈ K)
    (hbe : b1A * b2A ∈ K) (ht : tA ∈ K) : sQA45 ≤ K := by
  unfold sQA45
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hu
  · exact hal
  · exact hbe
  · exact ht

private theorem sElt_mem_conj_set {r : A45} (j : ℕ) (hr : wordElt (rWords.getD j []) = r)
    (i : ℕ) (hi : i < 5) (hj : j < 5) :
    sElt ((conjCodes.getD i []).getD j 0) ∈
      {x : A45 | ∃ n ∈ Subgroup.normalizer (sQA45 : Set A45), x = n * r * n⁻¹} :=
  ⟨wordElt (nWords.getD i []), wordElt_mem_normalizer i hi, by
    rw [← hr]
    exact (mul_inv_eq_iff_eq_mul.2 (conj_code_elt i j hi hj)).symm⟩

private theorem sQA45_le_closure_conj_t :
    sQA45 ≤ Subgroup.closure
      {x : A45 | ∃ n ∈ Subgroup.normalizer (sQA45 : Set A45), x = n * tA * n⁻¹} := by
  set Y : Set A45 := {x : A45 | ∃ n ∈ Subgroup.normalizer (sQA45 : Set A45), x = n * tA * n⁻¹}
    with hY
  have hr : wordElt (rWords.getD 3 []) = tA := tA_eq.symm
  have c0 : sElt 0 ∈ Subgroup.closure Y := by
    rw [sElt_zero]
    exact one_mem _
  have c1 : sElt 15 ∈ Subgroup.closure Y :=
    Subgroup.subset_closure (sElt_mem_conj_set 3 hr 0 (by norm_num) (by norm_num))
  have c2 : sElt 13 ∈ Subgroup.closure Y :=
    Subgroup.subset_closure (sElt_mem_conj_set 3 hr 1 (by norm_num) (by norm_num))
  have c3 : sElt 1 ∈ Subgroup.closure Y :=
    Subgroup.subset_closure (sElt_mem_conj_set 3 hr 2 (by norm_num) (by norm_num))
  have c4 : sElt 8 ∈ Subgroup.closure Y := by
    refine Subgroup.subset_closure ⟨1, one_mem _, ?_⟩
    have h : sElt 8 = tA := by simp [sElt]
    rw [h]
    simp
  refine sQA45_le_of_gens ?_ ?_ ?_ ?_
  · rw [gen_eq_prod (e := (toW lU, 1, 0, 0, 0)) (by decide) uA_eq]
    exact mul_mem (mul_mem c3 c0) (mul_mem c0 c0)
  · rw [gen_eq_prod (e := (toW lAl, 15, 13, 0, 0)) (by decide) alA_eq]
    exact mul_mem (mul_mem c1 c2) (mul_mem c0 c0)
  · rw [gen_eq_prod (e := (toW lBe, 8, 13, 1, 0)) (by decide) beA_eq]
    exact mul_mem (mul_mem c4 c2) (mul_mem c3 c0)
  · rw [gen_eq_prod (e := (toW lT, 8, 0, 0, 0)) (by decide) tA_eq]
    exact mul_mem (mul_mem c4 c0) (mul_mem c0 c0)

private theorem sQA45_le_closure_conj_ut :
    sQA45 ≤ Subgroup.closure
      {x : A45 | ∃ n ∈ Subgroup.normalizer (sQA45 : Set A45), x = n * (uA * tA) * n⁻¹} := by
  set Y : Set A45 :=
    {x : A45 | ∃ n ∈ Subgroup.normalizer (sQA45 : Set A45), x = n * (uA * tA) * n⁻¹} with hY
  have hr : wordElt (rWords.getD 4 []) = uA * tA := by
    change wordElt (toW lU ++ toW lT) = uA * tA
    have e1 : wordElt (toW lU) = uA := uA_eq.symm
    have e2 : wordElt (toW lT) = tA := tA_eq.symm
    rw [wordElt_append, e1, e2]
  have c0 : sElt 0 ∈ Subgroup.closure Y := by
    rw [sElt_zero]
    exact one_mem _
  have c1 : sElt 2 ∈ Subgroup.closure Y :=
    Subgroup.subset_closure (sElt_mem_conj_set 4 hr 1 (by norm_num) (by norm_num))
  have c2 : sElt 5 ∈ Subgroup.closure Y :=
    Subgroup.subset_closure (sElt_mem_conj_set 4 hr 3 (by norm_num) (by norm_num))
  have c3 : sElt 10 ∈ Subgroup.closure Y :=
    Subgroup.subset_closure (sElt_mem_conj_set 4 hr 4 (by norm_num) (by norm_num))
  have c4 : sElt 9 ∈ Subgroup.closure Y := by
    refine Subgroup.subset_closure ⟨1, one_mem _, ?_⟩
    have h : sElt 9 = uA * tA := by simp [sElt]
    rw [h]
    simp
  refine sQA45_le_of_gens ?_ ?_ ?_ ?_
  · rw [gen_eq_prod (e := (toW lU, 9, 2, 10, 0)) (by decide) uA_eq]
    exact mul_mem (mul_mem c4 c1) (mul_mem c3 c0)
  · rw [gen_eq_prod (e := (toW lAl, 2, 0, 0, 0)) (by decide) alA_eq]
    exact mul_mem (mul_mem c1 c0) (mul_mem c0 c0)
  · rw [gen_eq_prod (e := (toW lBe, 9, 2, 5, 10)) (by decide) beA_eq]
    exact mul_mem (mul_mem c4 c1) (mul_mem c2 c3)
  · rw [gen_eq_prod (e := (toW lT, 2, 10, 0, 0)) (by decide) tA_eq]
    exact mul_mem (mul_mem c1 c3) (mul_mem c0 c0)

section Irreducible


theorem sQA45_le_closure_normalizer_conj (s : A45) (hs : s ∈ sQA45) (hs1 : s ≠ 1) :
    sQA45 ≤ Subgroup.closure
      {x : A45 | ∃ n ∈ Subgroup.normalizer (sQA45 : Set A45), x = n * s * n⁻¹} := by
  have key : ∀ r : A45, (∃ g ∈ Subgroup.normalizer (sQA45 : Set A45), g * r * g⁻¹ = s) →
      Subgroup.closure
        {x : A45 | ∃ n ∈ Subgroup.normalizer (sQA45 : Set A45), x = n * r * n⁻¹} ≤
      Subgroup.closure
        {x : A45 | ∃ n ∈ Subgroup.normalizer (sQA45 : Set A45), x = n * s * n⁻¹} := by
    intro r ⟨g, hg, hgr⟩
    rw [Subgroup.closure_le]
    rintro x ⟨m, hm, rfl⟩
    refine Subgroup.subset_closure ⟨m * g⁻¹, mul_mem hm (inv_mem hg), ?_⟩
    rw [← hgr]
    group
  rcases (qa45_normalizer_sQA45).2.2.2.1 s hs hs1 with h | h
  · exact sQA45_le_closure_conj_t.trans (key _ h)
  · exact sQA45_le_closure_conj_ut.trans (key _ h)

end Irreducible

end Normalizer

section Cover


private theorem spinFixes_add {g : A45} {x y : V} (hx : SpinFixes g x) (hy : SpinFixes g y) :
    SpinFixes g (x + y) := by
  unfold SpinFixes at *
  rw [Matrix.mulVec_add, hx, hy]

private theorem spinFixes_t_of_mem {u : V} (hu : u ∈ spinFixS) : SpinFixes tA u :=
  (mem_spinFixS_iff u).1 hu tA tA_mem_S

private theorem spinFixes_t_compV (k : ℕ) : SpinFixes tA (compV k) := by
  have h1 : SpinFixes tA (vecOfNat c1m) := (fixesT_iff _).2 (by
    rw [bitmask_vecOfNat _ c1m_lt]
    exact c1m_fixesT)
  have h2 : SpinFixes tA (vecOfNat c2m) := (fixesT_iff _).2 (by
    rw [bitmask_vecOfNat _ c2m_lt]
    exact c2m_fixesT)
  have h0 : SpinFixes tA (0 : V) := by
    unfold SpinFixes
    rw [Matrix.mulVec_zero]
  unfold compV
  refine spinFixes_add ?_ ?_
  · split_ifs
    · exact h1
    · exact h0
  · split_ifs
    · exact h2
    · exact h0

private theorem eps_on_C (ε : V → ZMod 2)
    (hadd : ∀ x, SpinFixes tA x → ∀ x', SpinFixes tA x' → ε (x + x') = ε x + ε x')
    (hW : ∀ u ∈ spinFixS, ε u = 0) (c : V) (hc : SpinFixes tA c) :
    ε c = epsOf (ε (vecOfNat c1m)) (ε (vecOfNat c2m)) (bitmask c) := by
  obtain ⟨k, hk⟩ : ∃ k, cosetIdx (bitmask c) = k := ⟨_, rfl⟩
  have hk4 : k < 4 := hk ▸ cosetIdx_lt _
  have hw : c + compV k ∈ spinFixS := by
    refine (fixesS_iff _).2 ?_
    rw [bitmask_add, bitmask_compV, ← hk]
    exact coset_check _ (bitmask_lt c) ((fixesT_iff c).1 hc)
  have hc' : c = (c + compV k) + compV k := by
    rw [add_assoc, v_add_self, add_zero]
  have h1 : ε c = ε (compV k) := by
    conv_lhs => rw [hc']
    rw [hadd _ (spinFixes_t_of_mem hw) _ (spinFixes_t_compV k), hW _ hw, zero_add]
  rw [h1]
  have h0 : ε 0 = 0 := hW 0 (zero_mem _)
  have hT1 : SpinFixes tA (vecOfNat c1m) := (fixesT_iff _).2 (by
    rw [bitmask_vecOfNat _ c1m_lt]
    exact c1m_fixesT)
  have hT2 : SpinFixes tA (vecOfNat c2m) := (fixesT_iff _).2 (by
    rw [bitmask_vecOfNat _ c2m_lt]
    exact c2m_fixesT)
  unfold epsOf
  rw [hk]
  interval_cases k
  · simp [compV, h0]
  · simp [compV]
  · simp [compV]
  · simp [compV, hadd _ hT1 _ hT2]

private abbrev aElt (i : Fin 3) : A45 := wordElt (aWord i)

private theorem aElt_conj_mem (i : Fin 3) : (aElt i)⁻¹ * tA * aElt i ∈ sQA45 := by
  have h : tA * aElt i = aElt i * sElt (aCode i) := by
    have h1 : wordElt (toW lT) = tA := tA_eq.symm
    have h2 := eq_of_word_tcomp (aCode_ok i)
    rw [h1, ← sElt_eq_word] at h2
    exact h2
  have h2 : (aElt i)⁻¹ * tA * aElt i = sElt (aCode i) := by
    rw [mul_assoc, h, inv_mul_cancel_left]
  rw [h2]
  exact sElt_mem _

theorem exists_conj_cover_of_fixes_tA (ε : V → ZMod 2)
    (hadd : ∀ x, SpinFixes tA x → ∀ x', SpinFixes tA x' → ε (x + x') = ε x + ε x')
    (hW : ∀ u ∈ spinFixS, ε u = 0) (v : V) (hv : SpinFixes tA v) (hq : q v = ε v) :
    ∃ a : A45, a⁻¹ * tA * a ∈ sQA45 ∧
      ∀ u ∈ spinFixS, ε (((rhoA a : GL8) : Mat8) *ᵥ u) = b v (((rhoA a : GL8) : Mat8) *ᵥ u) := by
  have hqv : ((qTab.getD (bitmask v) 0 : ℕ) : ZMod 2) =
      epsOf (ε (vecOfNat c1m)) (ε (vecOfNat c2m)) (bitmask v) :=
    (q_eq_cast v).symm.trans (hq.trans (eps_on_C ε hadd hW v hv))
  obtain ⟨i, hi⟩ := cover_check _ _ (bitmask v) (bitmask_lt v) ((fixesT_iff v).1 hv) hqv
  refine ⟨aElt i, aElt_conj_mem i, fun u hu => ?_⟩
  have hx : SpinFixes tA (((rhoA (aElt i) : GL8) : Mat8) *ᵥ u) :=
    spinFixes_mulVec_of_conj ((mem_spinFixS_iff u).1 hu _ (aElt_conj_mem i))
  have hbm : bitmask (((rhoA (aElt i) : GL8) : Mat8) *ᵥ u) =
      bapply (evalB b3 (aWord i)) (bitmask u) := by
    rw [← bapply_colsOf, ← spinMat_apply]
    exact congrArg (fun A => bapply A (bitmask u)) (colsOf_spinMat_word (aWord i))
  rw [eps_on_C ε hadd hW _ hx, b_eq_cast, hbm]
  exact hi _ ((fixesS_iff_mem_wMasks _ (bitmask_lt u)).1 ((fixesS_iff u).1 hu))

end Cover

end CFSG.RankThree.GF2n.Parrott

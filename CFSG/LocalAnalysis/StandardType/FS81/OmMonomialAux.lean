module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg
import TauCeti.Data.Finset.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

variable {n : ℕ}

@[expose] def omm_Hyp (P : Matrix (Fin n) (Fin n) (ZMod 3)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (s : Fin n → ZMod 3), IsSign s → ∏ i, s i = 1 →
    ∃ (σ' : Equiv.Perm (Fin n)) (s' : Fin n → ZMod 3), IsSign s' ∧ ∏ i, s' i = 1 ∧
      spMat σ s * P = P * spMat σ' s'

@[expose] def omm_supp (v : Fin n → ZMod 3) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i ≠ 0)

lemma omm_mem_supp {v : Fin n → ZMod 3} {i : Fin n} :
    i ∈ omm_supp v ↔ v i ≠ 0 := by
  simp [omm_supp]

lemma omm_sign_eq (z : ZMod 3) (hz : z ≠ 0) : z = 1 ∨ z = -1 := by
  decide +revert

lemma omm_sign_ne_zero {s : Fin n → ZMod 3} (hs : IsSign s) (i : Fin n) :
    s i ≠ 0 := by
  rcases hs i with h | h <;> rw [h] <;> decide

lemma omm_spMat_mulVec_single (σ : Equiv.Perm (Fin n)) (s : Fin n → ZMod 3)
    (j : Fin n) : spMat σ s *ᵥ Pi.single j 1 = Pi.single (σ j) (s j) := by
  rw [Matrix.mulVec_single_one]
  funext i
  simp [Matrix.col_apply, spMat_apply, Pi.single_apply]

lemma omm_single_eq_smul (j : Fin n) (c : ZMod 3) :
    Pi.single j c = c • Pi.single j (1 : ZMod 3) := by
  funext i
  by_cases h : i = j <;> simp [Pi.single_apply, h]

lemma omm_col_action_eq {P : Matrix (Fin n) (Fin n) (ZMod 3)}
    (σ : Equiv.Perm (Fin n)) (s : Fin n → ZMod 3) (σ' : Equiv.Perm (Fin n))
    (s' : Fin n → ZMod 3) (heq : spMat σ s * P = P * spMat σ' s') (l : Fin n) :
    spMat σ s *ᵥ P.col l = s' l • P.col (σ' l) := by
  calc spMat σ s *ᵥ P.col l
      = spMat σ s *ᵥ (P *ᵥ Pi.single l 1) := by rw [Matrix.mulVec_single_one]
    _ = (spMat σ s * P) *ᵥ Pi.single l 1 := by rw [Matrix.mulVec_mulVec]
    _ = (P * spMat σ' s') *ᵥ Pi.single l 1 := by rw [heq]
    _ = P *ᵥ (spMat σ' s' *ᵥ Pi.single l 1) := by rw [Matrix.mulVec_mulVec]
    _ = P *ᵥ Pi.single (σ' l) (s' l) := by rw [omm_spMat_mulVec_single]
    _ = s' l • P.col (σ' l) := by
        rw [omm_single_eq_smul, Matrix.mulVec_smul, Matrix.mulVec_single_one]

lemma omm_supp_smul {c : ZMod 3} (hc : c ≠ 0) (v : Fin n → ZMod 3) :
    omm_supp (c • v) = omm_supp v := by
  unfold omm_supp
  apply Finset.filter_congr
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero hc h⟩

lemma omm_supp_spMat_one (f v : Fin n → ZMod 3) (hf : IsSign f) :
    omm_supp (spMat 1 f *ᵥ v) = omm_supp v := by
  have hfun : spMat 1 f *ᵥ v = fun i => f i * v i := by
    funext i
    rw [spMat_mulVec]
    rfl
  rw [hfun]
  unfold omm_supp
  apply Finset.filter_congr
  intro i _
  rw [mul_ne_zero_iff]
  constructor
  · rintro ⟨-, hv⟩
    exact hv
  · intro hv
    refine ⟨?_, hv⟩
    rcases hf i with h1 | h1 <;> rw [h1] <;> decide

lemma omm_supp_spMat_perm (τ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 3) :
    omm_supp (spMat τ 1 *ᵥ v) = (omm_supp v).image τ := by
  have hfun : spMat τ 1 *ᵥ v = fun i => v (τ.symm i) := by
    funext i
    rw [spMat_mulVec]
    simp
  rw [hfun]
  unfold omm_supp
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    exact ⟨τ.symm i, h, Equiv.apply_symm_apply τ i⟩
  · rintro ⟨j, hj, rfl⟩
    simpa using hj

lemma omm_image_swap {A B : Finset (Fin n)} {a c : Fin n} (haB : a ∉ B)
    (hcB : c ∉ B) (hA : A = insert a B) : A.image (Equiv.swap a c) = insert c B := by
  rw [hA, Finset.image_insert]
  congr 1
  · simp
  · rw [show B.image (Equiv.swap a c) = B.image id from
        Finset.image_congr fun b hb =>
          Equiv.swap_apply_of_ne_of_ne (fun h => haB (h ▸ hb)) (fun h => hcB (h ▸ hb)),
      Finset.image_id]

lemma omm_prod_sign_bool {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Bool) :
    (∏ j ∈ s, (if t j then (-1 : ZMod 3) else 1)) = 1 ∨
      (∏ j ∈ s, (if t j then (-1 : ZMod 3) else 1)) = -1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases ih with h | h
      · by_cases ht : t a
        · right; rw [if_pos ht, h]; decide
        · left; rw [if_neg ht, h]; decide
      · by_cases ht : t a
        · left; rw [if_pos ht, h]; decide
        · right; rw [if_neg ht, h]; decide

@[expose] def omm_pattern (A : Finset (Fin n)) (t : A → Bool) : Fin n → ZMod 3 :=
  fun i => if hi : i ∈ A then (if t ⟨i, hi⟩ then -1 else 1) else 1

@[expose] def omm_lt_extend (A : Finset (Fin n)) (d : Fin n) (t : A → Bool) : Fin n → ZMod 3 :=
  fun i =>
    if hi : i ∈ A then omm_pattern A t i
    else if i = d then ∏ j : A, (if t j then (-1 : ZMod 3) else 1)
    else 1

lemma omm_lt_extend_sign (A : Finset (Fin n)) (d : Fin n) (t : A → Bool) :
    IsSign (omm_lt_extend A d t) := by
  intro i
  unfold omm_lt_extend
  by_cases hA : i ∈ A
  · rw [dif_pos hA]
    unfold omm_pattern
    rw [dif_pos hA]
    by_cases ht : t ⟨i, hA⟩ <;> simp [ht]
  · rw [dif_neg hA]
    by_cases hd : i = d
    · rw [if_pos hd]
      exact omm_prod_sign_bool (Finset.univ : Finset A) t
    · rw [if_neg hd]
      exact Or.inl rfl

lemma omm_prod_pattern (A : Finset (Fin n)) (d : Fin n) (hd : d ∉ A) (t : A → Bool) :
    (∏ i : Fin n, omm_lt_extend A d t i) = 1 := by
  set PA : ZMod 3 := ∏ j : A, (if t j then (-1 : ZMod 3) else 1) with hPA
  have hPA2 : PA * PA = 1 := by
    have h := omm_prod_sign_bool (Finset.univ : Finset A) t
    have h' : PA = 1 ∨ PA = -1 := by
      simpa [hPA] using h
    rcases h' with h1 | h1 <;> rw [h1] <;> decide
  have hsplit : (∏ i : Fin n, omm_lt_extend A d t i) =
      (∏ i ∈ A, omm_lt_extend A d t i) * (∏ i ∈ Aᶜ, omm_lt_extend A d t i) := by
    rw [← Finset.union_compl A, Finset.prod_union disjoint_compl_right]
  have hAprod : (∏ i ∈ A, omm_lt_extend A d t i) = PA := by
    rw [hPA, Finset.prod_subtype A (fun x => Iff.rfl)
      (fun j : Fin n => omm_lt_extend A d t j)]
    apply Finset.prod_congr rfl
    intro j _
    unfold omm_lt_extend omm_pattern
    rw [dif_pos j.2, dif_pos j.2]
  have hdA : d ∈ Aᶜ := by simpa using hd
  have hCompl : (∏ i ∈ Aᶜ, omm_lt_extend A d t i) = PA := by
    rw [Finset.prod_eq_single d]
    · unfold omm_lt_extend
      rw [dif_neg (by simpa using hdA), if_pos rfl]
    · intro i hi hne
      unfold omm_lt_extend
      rw [dif_neg (by simpa using hi), if_neg hne]
    · intro hdnot
      exact absurd hdA hdnot
  rw [hsplit, hAprod, hCompl, hPA2]

lemma omm_lt_extend_injOn (A : Finset (Fin n)) (d : Fin n) (t t' : A → Bool)
    (h : ∀ i ∈ A, omm_lt_extend A d t i = omm_lt_extend A d t' i) : t = t' := by
  funext j
  have hj := h j.1 j.2
  unfold omm_lt_extend at hj
  rw [dif_pos j.2, dif_pos j.2] at hj
  unfold omm_pattern at hj
  rw [dif_pos j.2, dif_pos j.2] at hj
  by_cases ht : t j
  · by_cases ht' : t' j
    · simp [ht, ht']
    · rw [if_pos ht, if_neg ht'] at hj
      exact absurd hj (by decide)
  · by_cases ht' : t' j
    · rw [if_neg ht, if_pos ht'] at hj
      exact absurd hj.symm (by decide)
    · simp [ht, ht']

lemma omm_card_param_le {P : Matrix (Fin n) (Fin n) (ZMod 3)} (h : omm_Hyp P)
    {ι : Type*} [Fintype ι] (l : Fin n) (f : ι → Fin n → ZMod 3)
    (hsign : ∀ i, IsSign (f i)) (hprod : ∀ i, ∏ j, f i j = 1)
    (hinj : ∀ i i', (∀ j ∈ omm_supp (P.col l), f i j = f i' j) → i = i') :
    Fintype.card ι ≤
      2 * (Finset.univ.filter (fun l' => omm_supp (P.col l') = omm_supp (P.col l))).card := by
  classical
  choose σ' s' hs' hp' heq' using fun i => h (1 : Equiv.Perm (Fin n)) (f i) (hsign i) (hprod i)
  let Φ : ι → Fin n × ZMod 3 := fun i => (σ' i l, s' i l)
  have hΦinj : Function.Injective Φ := by
    intro i i' hii
    have hσ : σ' i l = σ' i' l := congrArg Prod.fst hii
    have hs : s' i l = s' i' l := congrArg Prod.snd hii
    have h1 : spMat (1 : Equiv.Perm (Fin n)) (f i) *ᵥ P.col l = s' i l • P.col (σ' i l) :=
      omm_col_action_eq _ _ _ _ (heq' i) l
    have h2 : spMat (1 : Equiv.Perm (Fin n)) (f i') *ᵥ P.col l = s' i' l • P.col (σ' i' l) :=
      omm_col_action_eq _ _ _ _ (heq' i') l
    have hfun : spMat (1 : Equiv.Perm (Fin n)) (f i) *ᵥ P.col l =
        spMat (1 : Equiv.Perm (Fin n)) (f i') *ᵥ P.col l := by
      rw [h1, h2, hσ, hs]
    refine hinj i i' fun j hj => ?_
    have hfun2 := congrFun hfun j
    have hsp1 : (spMat (1 : Equiv.Perm (Fin n)) (f i) *ᵥ P.col l) j = f i j * P j l := by
      rw [spMat_mulVec]; rfl
    have hsp2 : (spMat (1 : Equiv.Perm (Fin n)) (f i') *ᵥ P.col l) j = f i' j * P j l := by
      rw [spMat_mulVec]; rfl
    rw [hsp1, hsp2] at hfun2
    exact mul_right_cancel₀ (Finset.mem_filter.mp hj).2 hfun2
  have hsub : Finset.univ.image Φ ⊆
      (Finset.univ.filter (fun l' => omm_supp (P.col l') = omm_supp (P.col l))) ×ˢ
        ({1, -1} : Finset (ZMod 3)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · have h1 : spMat (1 : Equiv.Perm (Fin n)) (f i) *ᵥ P.col l =
          s' i l • P.col (σ' i l) := omm_col_action_eq _ _ _ _ (heq' i) l
      have hs : omm_supp (s' i l • P.col (σ' i l)) = omm_supp (P.col (σ' i l)) :=
        omm_supp_smul (omm_sign_ne_zero (hs' i) l) _
      have hsupp : omm_supp (P.col (σ' i l)) = omm_supp (P.col l) := by
        rw [← hs, ← h1, omm_supp_spMat_one (f i) (P.col l) (hsign i)]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupp⟩
    · rcases omm_sign_eq (s' i l) (omm_sign_ne_zero (hs' i) l) with h1 | h1
      · rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (by simpa [Φ] using h1)
      · rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (by simpa [Φ] using h1)
  have hcard_le : (Finset.univ.image Φ).card ≤
      ((Finset.univ.filter (fun l' => omm_supp (P.col l') = omm_supp (P.col l))) ×ˢ
        ({1, -1} : Finset (ZMod 3))).card := Finset.card_le_card hsub
  have himg : (Finset.univ.image Φ).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hΦinj, Finset.card_univ]
  rw [himg, Finset.card_product, show ({1, -1} : Finset (ZMod 3)).card = 2 by decide] at hcard_le
  simpa [Nat.mul_comm] using hcard_le

lemma omm_perm_bound {P : Matrix (Fin n) (Fin n) (ZMod 3)} (h : omm_Hyp P)
    (l : Fin n) (a : Fin n) (ha : a ∈ omm_supp (P.col l)) :
    (n - (omm_supp (P.col l)).card + 1) *
      (Finset.univ.filter (fun l' => omm_supp (P.col l') = omm_supp (P.col l))).card ≤ n := by
  classical
  set A := omm_supp (P.col l) with hA
  set B := A.erase a with hB
  have haB : a ∉ B := Finset.notMem_erase a A
  have hAcard : A.card = B.card + 1 := (Finset.card_erase_add_one ha).symm
  have hchoose : ∀ c : {c : Fin n // c ∉ B},
      ∃ (σ' : Equiv.Perm (Fin n)) (s' : Fin n → ZMod 3), IsSign s' ∧ ∏ i, s' i = 1 ∧
        spMat (Equiv.swap a c.1) 1 * P = P * spMat σ' s' :=
    fun c => h (Equiv.swap a c.1) (fun _ => 1) (by intro i; exact Or.inl rfl) (by simp)
  choose σc sc hsc hpc heqc using hchoose
  let Ψ : {c : Fin n // c ∉ B} × {l' : Fin n // omm_supp (P.col l') = A} → Fin n :=
    fun p => σc p.1 p.2.1
  have hsupp_of (c : {c : Fin n // c ∉ B}) (l' : {l' : Fin n // omm_supp (P.col l') = A}) :
      omm_supp (P.col (σc c l'.1)) = insert c.1 B := by
    have hact := omm_col_action_eq (Equiv.swap a c.1) 1 (σc c) (sc c) (heqc c) l'.1
    have hs : omm_supp (sc c l'.1 • P.col (σc c l'.1)) = omm_supp (P.col (σc c l'.1)) :=
      omm_supp_smul (omm_sign_ne_zero (hsc c) l'.1) _
    rw [← hs, ← hact, omm_supp_spMat_perm, l'.2, hA]
    exact omm_image_swap haB c.2 (Finset.insert_erase ha).symm
  have hΨ : Function.Injective Ψ := by
    rintro ⟨c, l'⟩ ⟨c', l''⟩ heq
    have h1 := hsupp_of c l'
    have h2 := hsupp_of c' l''
    have hcc : c.1 = c'.1 := by
      have hcc' : (σc c) l'.1 = (σc c') l''.1 := by simpa using heq
      have himg : insert c.1 B = insert c'.1 B := by rw [← h1, hcc', h2]
      have hmem : c.1 ∈ insert c'.1 B := by
        rw [← himg]
        exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp hmem with hmem | hmem
      · exact hmem
      · exact absurd hmem c.2
    have hc : c = c' := Subtype.ext hcc
    subst hc
    have hll : l'.1 = l''.1 := by
      have hh : (σc c) l'.1 = (σc c) l''.1 := heq
      simpa using congrArg (σc c).symm hh
    exact Prod.ext rfl (Subtype.ext hll)
  have hcard : Fintype.card
      ({c : Fin n // c ∉ B} × {l' : Fin n // omm_supp (P.col l') = A}) ≤ n := by
    simpa using Fintype.card_le_of_injective Ψ hΨ
  have hcard1 : Fintype.card {c : Fin n // c ∉ B} = n - B.card := by
    rw [Fintype.card_subtype_compl (fun c : Fin n => c ∈ B), Fintype.card_coe,
      Fintype.card_fin]
  have hcard2 : Fintype.card {l' : Fin n // omm_supp (P.col l') = A} =
      (Finset.univ.filter (fun l' => omm_supp (P.col l') = A)).card := by
    rw [Fintype.card_subtype]
  rw [Fintype.card_prod, hcard1, hcard2] at hcard
  have hAle : A.card ≤ n := by
    calc A.card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ A)
      _ = n := by simp
  have hsub : n - B.card = n - A.card + 1 := by omega
  rw [hsub] at hcard
  rwa [hA] at hcard

end CFSG.StandardType.FrameRoute.FS81

end

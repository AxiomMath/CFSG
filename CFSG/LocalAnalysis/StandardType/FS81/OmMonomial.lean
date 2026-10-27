module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
import CFSG.LocalAnalysis.StandardType.FS81.OmMonomialAux
import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg
import TauCeti.Data.Finset.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

variable {n : ℕ}

private lemma omm_two_mul_lt_two_pow_pred (n : ℕ) (hn : 5 ≤ n) : 2 * n < 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have h2 : 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
        calc 2 ^ (n + 1 - 1) = 2 ^ n := by rw [Nat.add_sub_cancel]
          _ = 2 ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
          _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
          _ = 2 * 2 ^ (n - 1) := by ring
      rw [h2]
      have h3 : n + 1 < 2 ^ (n - 1) := by omega
      omega

private lemma omm_lt_arith {n w : ℕ} (hn : 5 ≤ n) (hw2 : 2 ≤ w) (hwn : w < n) :
    n < (n - w + 1) * 2 ^ (w - 1) := by
  have hP2 : 2 ≤ 2 ^ (w - 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPw : w ≤ 2 ^ (w - 1) := by
    have h := (w - 1).lt_two_pow_self
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + w := ⟨n - w, by omega⟩
  have hm : 1 ≤ m := by omega
  rw [Nat.add_sub_cancel]
  nlinarith [hm, hP2, hPw]

private theorem omm_weight_one {P : Matrix (Fin n) (Fin n) (ZMod 3)} (hn : 5 ≤ n)
    (h : omm_Hyp P) (l : Fin n) : ¬ 2 ≤ (omm_supp (P.col l)).card := by
  intro hw2
  set A := omm_supp (P.col l) with hA
  set M := (Finset.univ.filter (fun l' => omm_supp (P.col l') = omm_supp (P.col l))).card
    with hM
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  have hAle : A.card ≤ n := by
    calc A.card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ A)
      _ = n := by simp
  have hperm : (n - A.card + 1) * M ≤ n :=
    omm_perm_bound h l a (by rw [← hA]; exact ha)
  by_cases hwn : A.card = n
  · have hAuniv : A = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ A)
      rw [hwn]
      simp
    let f : {S : Finset (Fin n) // Even S.card} → Fin n → ZMod 3 :=
      fun S i => if i ∈ S.1 then -1 else 1
    have hsign : ∀ S, IsSign (f S) := by
      intro S i
      by_cases h : i ∈ S.1 <;> simp [f, h]
    have hprod : ∀ S, ∏ i, f S i = 1 := by
      intro S
      have hS : Even S.1.card := S.2
      have h1 : (∏ i, f S i) = ∏ i, (if i ∈ S.1 then (-1 : ZMod 3) else 1) := rfl
      rw [h1, Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.prod_const, Finset.prod_const_one, mul_one]
      rcases hS with ⟨k, hk⟩
      rw [hk]
      exact Even.neg_one_pow (n := k + k) ⟨k, rfl⟩
    have hinj : ∀ S S', (∀ i ∈ A, f S i = f S' i) → S = S' := by
      intro S S' hagree
      apply Subtype.ext
      ext i
      have hi := hagree i (by rw [hAuniv]; exact Finset.mem_univ i)
      simp only [f] at hi
      by_cases hS : i ∈ S.1
      · by_cases hS' : i ∈ S'.1
        · simp [hS, hS']
        · rw [if_pos hS, if_neg hS'] at hi
          exact absurd hi (by decide)
      · by_cases hS' : i ∈ S'.1
        · rw [if_neg hS, if_pos hS'] at hi
          exact absurd hi.symm (by decide)
        · simp [hS, hS']
    have hbound := omm_card_param_le h l f hsign hprod hinj
    have hcard : Fintype.card {S : Finset (Fin n) // Even S.card} = 2 ^ (n - 1) := by
      rw [← Nat.card_eq_fintype_card, TauCeti.card_even_card_finset]
      simp
    rw [hcard] at hbound
    have hMn : M ≤ n := by
      rw [hM]
      calc (Finset.univ.filter (fun l' => omm_supp (P.col l') = A)).card
          ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
        _ = n := by simp
    have hgt : 2 * n < 2 ^ (n - 1) := omm_two_mul_lt_two_pow_pred n hn
    omega
  · have hlt : A.card < n := by omega
    obtain ⟨d, hdA⟩ : ∃ d : Fin n, d ∉ A := by
      have hcard : A.card < (Finset.univ : Finset (Fin n)).card := by simpa using hlt
      obtain ⟨d, _, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      exact ⟨d, hd⟩
    let f : (A → Bool) → Fin n → ZMod 3 := omm_lt_extend A d
    have hsign : ∀ t, IsSign (f t) := fun t => omm_lt_extend_sign A d t
    have hprod : ∀ t, ∏ i, f t i = 1 := fun t => omm_prod_pattern A d hdA t
    have hinj : ∀ t t', (∀ i ∈ A, f t i = f t' i) → t = t' :=
      fun t t' => omm_lt_extend_injOn A d t t'
    have hbound := omm_card_param_le h l f hsign hprod hinj
    have hcard : Fintype.card (A → Bool) = 2 ^ A.card := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    rw [hcard] at hbound
    have hMge : 2 ^ (A.card - 1) ≤ M := by
      have h2w : 2 ^ A.card = 2 * 2 ^ (A.card - 1) := by
        calc 2 ^ A.card = 2 ^ ((A.card - 1) + 1) := by
                rw [Nat.sub_add_cancel (by omega : 1 ≤ A.card)]
            _ = 2 ^ (A.card - 1) * 2 := pow_succ 2 (A.card - 1)
            _ = 2 * 2 ^ (A.card - 1) := by ring
      rw [h2w] at hbound
      exact le_of_mul_le_mul_left hbound (by norm_num)
    have harith : n < (n - A.card + 1) * 2 ^ (A.card - 1) := omm_lt_arith hn hw2 hlt
    have hchain : (n - A.card + 1) * 2 ^ (A.card - 1) ≤ n :=
      le_trans (Nat.mul_le_mul_left _ hMge) hperm
    omega

theorem monomial_of_conj_even {n : ℕ} (hn : 5 ≤ n) (P : Matrix (Fin n) (Fin n) (ZMod 3))
    (hP : IsUnit P.det)
    (h : ∀ (σ : Equiv.Perm (Fin n)) (s : Fin n → ZMod 3), IsSign s → ∏ i, s i = 1 →
      ∃ (σ' : Equiv.Perm (Fin n)) (s' : Fin n → ZMod 3), IsSign s' ∧ ∏ i, s' i = 1 ∧
        spMat σ s * P = P * spMat σ' s') :
    ∃ (σ : Equiv.Perm (Fin n)) (s : Fin n → ZMod 3), IsSign s ∧ P = spMat σ s := by
  classical
  have hPunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hP
  have hmul_inj := Matrix.mulVec_injective_of_isUnit hPunit
  have hcol_ne : ∀ l : Fin n, P.col l ≠ 0 := by
    intro l hzero
    have h1 : P *ᵥ Pi.single l 1 = P *ᵥ (0 : Fin n → ZMod 3) := by
      rw [Matrix.mulVec_single_one, hzero, Matrix.mulVec_zero]
    have h3 : (1 : ZMod 3) = 0 := by simpa using congrFun (hmul_inj h1) l
    exact one_ne_zero h3
  have huniq : ∀ l : Fin n, ∃! i : Fin n, P i l ≠ 0 := by
    intro l
    have hw := omm_weight_one hn h l
    have hne := hcol_ne l
    have hpos : 1 ≤ (omm_supp (P.col l)).card := by
      by_contra hlt
      have h0 : (omm_supp (P.col l)).card = 0 := by omega
      have hemp : omm_supp (P.col l) = ∅ := Finset.card_eq_zero.mp h0
      apply hne
      funext i
      have hi : i ∉ omm_supp (P.col l) := by rw [hemp]; exact Finset.notMem_empty i
      have h' : ¬ (P i l ≠ 0) := by
        intro hc
        exact hi ((omm_mem_supp (v := P.col l) (i := i)).mpr hc)
      exact not_not.mp h'
    have hcard : (omm_supp (P.col l)).card = 1 := by omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    refine ⟨i, ?_, ?_⟩
    · have : i ∈ omm_supp (P.col l) := by rw [hi]; exact Finset.mem_singleton_self i
      exact (omm_mem_supp (v := P.col l) (i := i)).mp this
    · intro j hj
      have : j ∈ omm_supp (P.col l) := (omm_mem_supp (v := P.col l) (i := j)).mpr hj
      rw [hi, Finset.mem_singleton] at this
      exact this
  let σ : Fin n → Fin n := fun l => Classical.choose (huniq l)
  have hσspec : ∀ l, P (σ l) l ≠ 0 := fun l => (Classical.choose_spec (huniq l)).1
  have hσuniq : ∀ l i, P i l ≠ 0 → i = σ l :=
    fun l i hi => (Classical.choose_spec (huniq l)).2 i hi
  have hcol_eq : ∀ l, P.col l = P (σ l) l • Pi.single (σ l) 1 := by
    intro l
    funext i
    by_cases hi : i = σ l
    · subst hi
      rw [Matrix.col_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · have hz : P i l = 0 := by
        by_contra hc
        exact hi (hσuniq l i hc)
      rw [Matrix.col_apply, hz, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_eq_mul, mul_zero]
  have hσinj : Function.Injective σ := by
    intro l l' hll
    by_contra hne
    have h1 : P *ᵥ Pi.single l 1 = P (σ l) l • Pi.single (σ l) 1 := by
      rw [Matrix.mulVec_single_one, hcol_eq]
    have h2 : P *ᵥ Pi.single l' 1 = P (σ l') l' • Pi.single (σ l') 1 := by
      rw [Matrix.mulVec_single_one, hcol_eq]
    have h3 : P *ᵥ (P (σ l') l' • Pi.single l 1) =
        P *ᵥ (P (σ l) l • Pi.single l' 1) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2, hll]
      exact smul_comm _ _ _
    have h5 : P (σ l') l' = 0 := by
      have h6 := congrFun (hmul_inj h3) l
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne,
        smul_eq_mul, smul_eq_mul, mul_one, mul_zero] at h6
      exact h6
    exact (hσspec l') h5
  let σe : Equiv.Perm (Fin n) := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσinj)
  refine ⟨σe, fun l => P (σ l) l, fun l => omm_sign_eq _ (hσspec l), ?_⟩
  ext i l
  rw [spMat_apply]
  by_cases hil : i = σe l
  · rw [if_pos hil]
    subst hil
    rfl
  · rw [if_neg hil]
    have hz : P i l = 0 := by
      by_contra hc
      exact hil (by rw [hσuniq l i hc]; rfl)
    rw [hz]

end CFSG.StandardType.FrameRoute.FS81

end

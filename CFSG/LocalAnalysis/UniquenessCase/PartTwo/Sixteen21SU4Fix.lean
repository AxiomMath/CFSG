module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Inputs

public section

open CFSG.Open

open scoped Matrix

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21

variable {K : Type} [Field K]

private theorem cube_eq_one [Finite K] (hK : Nat.card K = 4) {a : K} (ha : a ≠ 0) :
    a ^ 3 = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  have h4 : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rw [h4] at h
  rw [show 4 - 1 = 3 by norm_num] at h
  exact h

private lemma permMatrix_apply' (σ : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    σ.permMatrix K i j = if σ i = j then (1 : K) else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

private lemma diag_perm_apply (σ : Equiv.Perm (Fin 4)) (μ : Fin 4 → K) (i j : Fin 4) :
    (Matrix.diagonal μ * σ.permMatrix K) i j = if σ i = j then μ i else 0 := by
  rw [Matrix.diagonal_mul, permMatrix_apply']
  by_cases h : σ i = j <;> simp [h]

private lemma diag_perm_mul_self_apply (σ : Equiv.Perm (Fin 4)) (μ : Fin 4 → K)
    (i j : Fin 4) :
    ((Matrix.diagonal μ * σ.permMatrix K) * (Matrix.diagonal μ * σ.permMatrix K)) i j =
      if σ (σ i) = j then μ i * μ (σ i) else 0 := by
  rw [Matrix.mul_apply]
  simp only [diag_perm_apply]
  rw [show (∑ k, (if σ i = k then μ i else 0) * (if σ k = j then μ k else 0)) =
      ∑ k, (if σ i = k then μ i * (if σ k = j then μ k else 0) else 0) by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases h : σ i = k <;> simp [h]]
  rw [Fintype.sum_ite_eq]
  by_cases h : σ (σ i) = j <;> simp [h]

private lemma perm_pow_three_apply (σ : Equiv.Perm (Fin 4)) (hσ3 : σ ^ 3 = 1) (i : Fin 4) :
    σ (σ (σ i)) = i := by
  have h := congrArg (fun τ : Equiv.Perm (Fin 4) => τ i) hσ3
  simpa [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two] using h

private lemma diag_perm_cube_apply (σ : Equiv.Perm (Fin 4)) (hσ3 : σ ^ 3 = 1)
    (μ : Fin 4 → K) (i j : Fin 4) :
    (((Matrix.diagonal μ * σ.permMatrix K) * (Matrix.diagonal μ * σ.permMatrix K)) *
      (Matrix.diagonal μ * σ.permMatrix K)) i j =
      if i = j then μ i * μ (σ i) * μ (σ (σ i)) else 0 := by
  rw [Matrix.mul_apply]
  simp only [diag_perm_mul_self_apply, diag_perm_apply]
  rw [show (∑ k, (if σ (σ i) = k then μ i * μ (σ i) else 0) *
        (if σ k = j then μ k else 0)) =
      ∑ k, (if σ (σ i) = k then
        (μ i * μ (σ i)) * (if σ k = j then μ k else 0) else 0) by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases h : σ (σ i) = k <;> simp [h]]
  rw [Fintype.sum_ite_eq, perm_pow_three_apply σ hσ3 i]
  by_cases h : i = j <;> simp [h]

private lemma det_diag_perm (σ : Equiv.Perm (Fin 4)) (hsign : Equiv.Perm.sign σ = 1)
    (μ : Fin 4 → K) (hprod : ∏ i, μ i = 1) :
    (Matrix.diagonal μ * σ.permMatrix K).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation, hsign]
  simp [hprod]

private lemma diag_perm_unitary [Finite K] (hK : Nat.card K = 4)
    (σ : Equiv.Perm (Fin 4)) (μ : Fin 4 → K) (hμ : ∀ i, μ i ≠ 0) :
    ((Matrix.diagonal μ * σ.permMatrix K).map (· ^ 2))ᵀ *
      (Matrix.diagonal μ * σ.permMatrix K) = 1 := by
  ext c c'
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ.symm c)]
  · simp only [Matrix.transpose_apply, Matrix.map_apply, diag_perm_apply,
      Equiv.apply_symm_apply]
    rw [Matrix.one_apply]
    by_cases h : c = c'
    · rw [h]
      simp only [if_pos rfl]
      rw [← pow_succ, show 2 + 1 = 3 by norm_num]
      exact cube_eq_one hK (hμ _)
    · simp [h]
  · intro r _ hr
    simp only [Matrix.transpose_apply, Matrix.map_apply, diag_perm_apply]
    have hsrc : σ r ≠ c := by
      intro hcon
      exact hr (by rw [← hcon, Equiv.symm_apply_apply])
    rw [if_neg hsrc]
    simp
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

private lemma diag_perm_cube (σ : Equiv.Perm (Fin 4)) (hσ3 : σ ^ 3 = 1) (μ : Fin 4 → K)
    (hcyc : ∀ i, μ i * μ (σ i) * μ (σ (σ i)) = 1) :
    (Matrix.diagonal μ * σ.permMatrix K) ^ 3 = 1 := by
  have hpow : (Matrix.diagonal μ * σ.permMatrix K) ^ 3 =
      ((Matrix.diagonal μ * σ.permMatrix K) * (Matrix.diagonal μ * σ.permMatrix K)) *
        (Matrix.diagonal μ * σ.permMatrix K) := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
  rw [hpow]
  ext i j
  rw [diag_perm_cube_apply σ hσ3 μ i j]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, hcyc i, Matrix.one_apply_eq]
  · rw [if_neg h, Matrix.one_apply_ne h]

private lemma su_of_data [Finite K] (hK : Nat.card K = 4)
    {σ : Equiv.Perm (Fin 4)} {μ : Fin 4 → K}
    (hσ3 : σ ^ 3 = 1) (hsign : Equiv.Perm.sign σ = 1)
    (hμ : ∀ i, μ i ≠ 0) (hprod : ∏ i, μ i = 1)
    (hcyc : ∀ i, μ i * μ (σ i) * μ (σ (σ i)) = 1)
    (hA1 : Matrix.diagonal μ * σ.permMatrix K ≠ 1) :
    ∃ g : GL (Fin 4) K, g ∈ StatedSU 4 2 K ∧ g ^ 3 = 1 ∧ g ≠ 1 ∧
      (g : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal μ * σ.permMatrix K := by
  have hdet := det_diag_perm σ hsign μ hprod
  have huni := diag_perm_unitary hK σ μ hμ
  have hcube := diag_perm_cube σ hσ3 μ hcyc
  refine ⟨Matrix.GeneralLinearGroup.mk'' (Matrix.diagonal μ * σ.permMatrix K)
    (by rw [hdet]; exact isUnit_one), ?_, ?_, ?_, ?_⟩
  · exact Subgroup.subset_closure ⟨hdet, huni⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_one]
    exact hcube
  · intro hg
    apply hA1
    have h := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hg
    rw [Matrix.GeneralLinearGroup.coe_one] at h
    exact h
  · rfl

private lemma exists_order_three_fixing [Finite K] (hK : Nat.card K = 4)
    (x : Fin 4 → K) {σ : Equiv.Perm (Fin 4)} {μ : Fin 4 → K}
    (hσ3 : σ ^ 3 = 1) (hsign : Equiv.Perm.sign σ = 1)
    (hμ : ∀ i, μ i ≠ 0) (hprod : ∏ i, μ i = 1)
    (hcyc : ∀ i, μ i * μ (σ i) * μ (σ (σ i)) = 1)
    (hfix : ∀ i, μ i * x (σ i) = x i)
    (hA1 : Matrix.diagonal μ * σ.permMatrix K ≠ 1) :
    ∃ g ∈ StatedSU 4 2 K, orderOf g = 3 ∧
      Matrix.mulVec (g : Matrix (Fin 4) (Fin 4) K) x = x := by
  obtain ⟨g, hgmem, hg3, hg1, hgcoe⟩ := su_of_data hK hσ3 hsign hμ hprod hcyc hA1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨g, hgmem, orderOf_eq_prime hg3 hg1, ?_⟩
  rw [hgcoe]
  ext i
  rw [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec, Matrix.mulVec_diagonal]
  exact hfix i

private lemma prod_update_diag (i j : Fin 4) (hij : i ≠ j) (w : K) :
    ∏ r : Fin 4,
      Function.update (Function.update (fun _ => 1) i w) j (w ^ 2) r = w ^ 3 := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ j)]
  rw [Finset.prod_update_of_mem (by simp [Finset.mem_sdiff, hij])]
  simp
  ring

private lemma prod_update_cycle (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b c : K) :
    ∏ r : Fin 4,
      Function.update (Function.update (Function.update (fun _ => 1) i a) j b) k c r =
        a * b * c := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ k)]
  rw [Finset.prod_update_of_mem (by simp [Finset.mem_sdiff, hjk])]
  rw [Finset.prod_update_of_mem (by simp [Finset.mem_sdiff, hij, hik])]
  simp
  ring

private lemma diag_exists [Finite K] (hK : Nat.card K = 4)
    {w : K} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1)
    (i j : Fin 4) (hij : i ≠ j) (x : Fin 4 → K) (hxi : x i = 0) (hxj : x j = 0) :
    ∃ g ∈ StatedSU 4 2 K, orderOf g = 3 ∧
      Matrix.mulVec (g : Matrix (Fin 4) (Fin 4) K) x = x := by
  let μ : Fin 4 → K := Function.update (Function.update (fun _ => 1) i w) j (w ^ 2)
  have hμi : μ i = w := by simp [μ, hij]
  have hμj : μ j = w ^ 2 := by simp [μ, hij]
  have hμ : ∀ r, μ r ≠ 0 := by
    intro r
    by_cases hri : r = i
    · subst hri; rw [hμi]; exact hw0
    by_cases hrj : r = j
    · subst hrj; rw [hμj]; exact pow_ne_zero 2 hw0
    · simp [μ, hri, hrj]
  have hprod : ∏ r, μ r = 1 := by
    change (∏ r, Function.update (Function.update (fun _ => 1) i w) j (w ^ 2) r) = 1
    rw [prod_update_diag i j hij w, hw3]
  have hcyc : ∀ r, μ r * μ r * μ r = 1 := by
    intro r
    have h : μ r * μ r * μ r = μ r ^ 3 := by ring
    rw [h, cube_eq_one hK (hμ r)]
  have hfix : ∀ r, μ r * x r = x r := by
    intro r
    by_cases hri : r = i
    · subst hri; rw [hμi, hxi, mul_zero]
    by_cases hrj : r = j
    · subst hrj; rw [hμj, hxj, mul_zero]
    · simp [μ, hri, hrj]
  have hσ3 : (1 : Equiv.Perm (Fin 4)) ^ 3 = 1 := by simp
  have hsign : Equiv.Perm.sign (1 : Equiv.Perm (Fin 4)) = 1 := by simp
  have hA1 : Matrix.diagonal μ * (1 : Equiv.Perm (Fin 4)).permMatrix K ≠ 1 := by
    rw [Matrix.permMatrix_one, Matrix.mul_one]
    intro h
    have hii : μ i = 1 := by
      have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i i) h
      simpa using this
    exact hw1 (hμi.symm.trans hii)
  exact exists_order_three_fixing hK x hσ3 hsign hμ hprod hcyc hfix hA1

private lemma cycle_exists [Finite K] (hK : Nat.card K = 4)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : Fin 4 → K) (hxi : x i ≠ 0) (hxj : x j ≠ 0) (hxk : x k ≠ 0) :
    ∃ g ∈ StatedSU 4 2 K, orderOf g = 3 ∧
      Matrix.mulVec (g : Matrix (Fin 4) (Fin 4) K) x = x := by
  let μ : Fin 4 → K :=
    Function.update (Function.update (Function.update (fun _ => 1) i (x i / x j))
      j (x j / x k)) k (x k / x i)
  let σ : Equiv.Perm (Fin 4) := Equiv.swap j i * Equiv.swap j k
  have hμi : μ i = x i / x j := by simp [μ, hij, hik]
  have hμj : μ j = x j / x k := by simp [μ, hjk]
  have hμk : μ k = x k / x i := by simp [μ]
  have hμ : ∀ r, μ r ≠ 0 := by
    intro r
    by_cases hri : r = i
    · subst hri; rw [hμi]; exact div_ne_zero hxi hxj
    by_cases hrj : r = j
    · subst hrj; rw [hμj]; exact div_ne_zero hxj hxk
    by_cases hrk : r = k
    · subst hrk; rw [hμk]; exact div_ne_zero hxk hxi
    · simp [μ, hri, hrj, hrk]
  have habc : (x i / x j) * (x j / x k) * (x k / x i) = 1 := by
    field_simp
  have hbca : (x j / x k) * (x k / x i) * (x i / x j) = 1 := by
    rw [← habc]; ring
  have hcab : (x k / x i) * (x i / x j) * (x j / x k) = 1 := by
    rw [← habc]; ring
  have hσi : σ i = j := by
    simp only [σ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_right]
  have hσj : σ j = k := by
    simp only [σ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hjk) (Ne.symm hik)]
  have hσk : σ k = i := by
    simp only [σ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
  have hσr : ∀ r, r ≠ i → r ≠ j → r ≠ k → σ r = r := by
    intro r hri hrj hrk
    simp only [σ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hrj hrk, Equiv.swap_apply_of_ne_of_ne hrj hri]
  have h3c : σ.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hij) hjk hik
  have hσ3 : σ ^ 3 = 1 := by
    rw [← h3c.orderOf]
    exact pow_orderOf_eq_one σ
  have hsign : Equiv.Perm.sign σ = 1 := h3c.sign
  have hprod : ∏ r, μ r = 1 := by
    change (∏ r, Function.update (Function.update (Function.update (fun _ => 1) i (x i / x j))
      j (x j / x k)) k (x k / x i) r) = 1
    rw [prod_update_cycle i j k hij hik hjk (x i / x j) (x j / x k) (x k / x i), habc]
  have hcyc : ∀ r, μ r * μ (σ r) * μ (σ (σ r)) = 1 := by
    intro r
    by_cases hri : r = i
    · rw [hri] at *
      rw [hσi, hσj, hμi, hμj, hμk]
      exact habc
    by_cases hrj : r = j
    · rw [hrj] at *
      rw [hσj, hσk, hμj, hμk, hμi]
      exact hbca
    by_cases hrk : r = k
    · rw [hrk] at *
      rw [hσk, hσi, hμk, hμi, hμj]
      exact hcab
    · have hσr' : σ r = r := hσr r hri hrj hrk
      have hrr : σ (σ r) = r := by rw [hσr']; exact hσr'
      rw [hrr, hσr']
      simp [μ, hri, hrj, hrk]
  have hfix : ∀ r, μ r * x (σ r) = x r := by
    intro r
    by_cases hri : r = i
    · rw [hri] at *
      rw [hσi, hμi, div_mul_cancel₀ (x i) hxj]
    by_cases hrj : r = j
    · rw [hrj] at *
      rw [hσj, hμj, div_mul_cancel₀ (x j) hxk]
    by_cases hrk : r = k
    · rw [hrk] at *
      rw [hσk, hμk, div_mul_cancel₀ (x k) hxi]
    · rw [hσr r hri hrj hrk]
      simp [μ, hri, hrj, hrk]
  have hA1 : Matrix.diagonal μ * σ.permMatrix K ≠ 1 := by
    intro h
    have hii : (Matrix.diagonal μ * σ.permMatrix K) i i =
        (1 : Matrix (Fin 4) (Fin 4) K) i i := by rw [h]
    rw [diag_perm_apply, if_neg (by rw [hσi]; exact Ne.symm hij),
      Matrix.one_apply_eq] at hii
    exact zero_ne_one hii
  exact exists_order_three_fixing hK x hσ3 hsign hμ hprod hcyc hfix hA1

theorem rSU4NatFix_holds : RSU4NatFix := by
  intro K _ _ hK x
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨u, hu⟩ :=
    exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by simp [hcardu])
  have hw0 : (u : K) ≠ 0 := u.ne_zero
  have hw3 : (u : K) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu] at h
    simpa using congrArg (fun z : Kˣ => (z : K)) h
  have hw1 : (u : K) ≠ 1 := by
    intro h
    have hu1 : u = 1 := Units.ext h
    rw [hu1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  by_cases h2 : ∃ i j : Fin 4, i ≠ j ∧ x i = 0 ∧ x j = 0
  · obtain ⟨i, j, hij, hxi, hxj⟩ := h2
    exact diag_exists hK hw0 hw1 hw3 i j hij x hxi hxj
  · have hnn : ∀ i j : Fin 4, i ≠ j → x i = 0 → x j ≠ 0 := by
      intro i j hij hi hj
      exact h2 ⟨i, j, hij, hi, hj⟩
    rcases eq_or_ne (x 0) 0 with h0 | h0
    · exact cycle_exists hK 1 2 3 (by decide) (by decide) (by decide) x
        (hnn 0 1 (by decide) h0) (hnn 0 2 (by decide) h0) (hnn 0 3 (by decide) h0)
    · rcases eq_or_ne (x 1) 0 with h1 | h1
      · exact cycle_exists hK 0 2 3 (by decide) (by decide) (by decide) x
          h0 (hnn 1 2 (by decide) h1) (hnn 1 3 (by decide) h1)
      · rcases eq_or_ne (x 2) 0 with h2z | h2z
        · exact cycle_exists hK 0 1 3 (by decide) (by decide) (by decide) x
            h0 h1 (hnn 2 3 (by decide) h2z)
        · exact cycle_exists hK 0 1 2 (by decide) (by decide) (by decide) x h0 h1 h2z

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21

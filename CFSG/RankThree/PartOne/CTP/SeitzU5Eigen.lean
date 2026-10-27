module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.RankThree.PartOne.CTP.U5Eigen

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] (σ : K ≃+* K)

def IsIsom (A : Matrix (Fin 5) (Fin 5) K) : Prop :=
  ∀ x y, herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y

theorem isIsom_of_conjTr {A : Matrix (Fin 5) (Fin 5) K} (h : conjTr σ A * A = 1) :
    IsIsom σ A := fun x y => by rw [herm_mulVec, h, Matrix.one_mulVec]

theorem IsIsom.mul {A B : Matrix (Fin 5) (Fin 5) K} (hA : IsIsom σ A) (hB : IsIsom σ B) :
    IsIsom σ (A * B) := fun x y => by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hB]

theorem isIsom_one : IsIsom σ (1 : Matrix (Fin 5) (Fin 5) K) := fun x y => by simp

theorem IsIsom.pow {A : Matrix (Fin 5) (Fin 5) K} (hA : IsIsom σ A) (k : ℕ) :
    IsIsom σ (A ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact isIsom_one σ
  | succ k ih => rw [pow_succ]; exact ih.mul σ hA

theorem herm_eq_zero_of_eigen {E : Matrix (Fin 5) (Fin 5) K} (hE : IsIsom σ E) {α β : K}
    {x y : Fin 5 → K} (hx : E *ᵥ x = α • x) (hy : E *ᵥ y = β • y) (hne : σ α * β ≠ 1) :
    herm σ x y = 0 := by
  have h := hE x y
  rw [hx, hy, herm_smul_left, herm_smul_right] at h
  have : (σ α * β - 1) * herm σ x y = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd (sub_eq_zero.mp h') hne
  · exact h'


theorem pow_mul_comm {E F : Matrix (Fin 5) (Fin 5) K} {ζ : K} (hEF : E * F = ζ • (F * E))
    (k : ℕ) : E * F ^ k = ζ ^ k • (F ^ k * E) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ']
    rw [← Matrix.mul_assoc, hEF, Matrix.smul_mul, Matrix.mul_assoc, ih, Matrix.mul_smul,
      smul_smul, Matrix.mul_assoc]

theorem pow_inj {ζ : K} (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) {i j : ℕ} (hi : i < 5) (hj : j < 5)
    (h : ζ ^ i = ζ ^ j) : i = j := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf ζ = 5 := orderOf_eq_prime hζ5 hζ1
  have hz0 : ζ ≠ 0 := by rintro rfl; simp at hζ5
  have key : ∀ i j : ℕ, i < j → j < 5 → ζ ^ i = ζ ^ j → False := by
    intro i j hij hj5 h
    have hz : ζ ^ i ≠ 0 := pow_ne_zero _ hz0
    have h' : ζ ^ i * ζ ^ (j - i) = ζ ^ i * 1 := by
      rw [← pow_add, mul_one, show i + (j - i) = j by omega]
      exact h.symm
    exact pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; omega) (mul_left_cancel₀ hz h')
  by_contra hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact key i j hlt hj h
  · exact key j i hgt hi h.symm

theorem herm_sum_left' {ι : Type*} (s : Finset ι) (g : ι → Fin 5 → K) (y : Fin 5 → K) :
    herm σ (∑ i ∈ s, g i) y = ∑ i ∈ s, herm σ (g i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_left, ih]

theorem herm_sum_right' {ι : Type*} (s : Finset ι) (x : Fin 5 → K) (g : ι → Fin 5 → K) :
    herm σ x (∑ i ∈ s, g i) = ∑ i ∈ s, herm σ x (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right, ih]

theorem exists_eigen (h2 : (2 : K) = 0)
    (hnorm5 : ∀ x : K, x ^ 5 = 1 → σ x * x = 1)
    {ζ : K} (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1)
    {E : Matrix (Fin 5) (Fin 5) K} (hE : IsIsom σ E) (hE5 : E ^ 5 = 1) :
    ∃ (j : ℕ) (u : Fin 5 → K), j < 5 ∧ herm σ u u ≠ 0 ∧ E *ᵥ u = ζ ^ j • u := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf ζ = 5 := orderOf_eq_prime hζ5 hζ1
  have hne : ∀ k : ℕ, 0 < k → k < 5 → ζ ^ k ≠ 1 := fun k hk hk5 =>
    pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; exact hk5)
  set w : Fin 5 → K := Pi.single 0 1 with hw
  set c : K := ζ ^ 4 with hc
  have hcz : ζ * c = 1 := by rw [hc, ← pow_succ']; exact hζ5
  set a : ℕ → (Fin 5 → K) := fun m => E ^ m *ᵥ w with ha
  have haE : ∀ m, E *ᵥ a m = a (m + 1) := fun m => by
    simp only [ha, Matrix.mulVec_mulVec, pow_succ']
  have ha5 : a 5 = a 0 := by simp [ha, hE5]
  let u : ℕ → (Fin 5 → K) := fun j => ∑ m ∈ Finset.range 5, c ^ (j * m) • a m
  have hEu : ∀ j, E *ᵥ u j = ζ ^ j • u j := by
    intro j
    simp only [u, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Matrix.mulVec_add,
      Matrix.mulVec_smul, haE, smul_add, smul_smul]
    rw [ha5]
    have hx1 : ζ ^ j * c ^ j = 1 := by rw [← mul_pow, hcz, one_pow]
    have hc4 : c ^ 4 = ζ := by
      rw [hc, ← pow_mul]
      calc ζ ^ (4 * 4) = ζ ^ (5 * 3) * ζ := by rw [← pow_succ]
        _ = ζ := by rw [pow_mul, hζ5, one_pow, one_mul]
    have hx2 : (c ^ j) ^ 4 = ζ ^ j := by rw [← pow_mul, mul_comm, pow_mul, hc4]
    simp only [pow_mul, Nat.reduceAdd, mul_zero, pow_zero, mul_one]
    ext r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(a 1 r) - c ^ j * a 2 r - (c ^ j) ^ 2 * a 3 r - (c ^ j) ^ 3 * a 4 r) * hx1
      + (a 0 r) * hx2
  have hc5 : c ^ 5 = 1 := by
    rw [hc, ← pow_mul, show 4 * 5 = 5 * 4 from rfl, pow_mul, hζ5, one_pow]
  have hgeom : ∀ m, 1 ≤ m → m ≤ 4 → ∑ j ∈ Finset.range 5, c ^ (j * m) = 0 := by
    intro m hm1 hm4
    have hcm : c ^ m ≠ 1 := by
      intro h1
      have h3 : ζ ^ (4 * m) = 1 := by rw [pow_mul, ← hc, h1]
      have h4 := (orderOf_dvd_iff_pow_eq_one).mpr h3
      rw [hord] at h4
      omega
    have h5 : (c ^ m) ^ 5 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hc5, one_pow]
    have := geom_sum_eq hcm 5
    rw [h5, sub_self, zero_div] at this
    simpa [pow_mul'] using this
  have hsum : ∑ j ∈ Finset.range 5, u j = w := by
    simp only [u]
    rw [Finset.sum_comm]
    have hm : ∀ m ∈ Finset.range 5, (∑ j ∈ Finset.range 5, c ^ (j * m)) • a m =
        if m = 0 then a 0 else 0 := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · have h5 : (5 : K) = 1 := by linear_combination 2 * h2
        simp [Finset.sum_const, h5]
      · have hm4 : m ≤ 4 := by have := Finset.mem_range.mp hm; omega
        rw [hgeom m hpos hm4, zero_smul]
        simp [Nat.pos_iff_ne_zero.mp hpos]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_congr rfl hm]
    simp [ha]
  have hnormζ : ∀ k : ℕ, σ (ζ ^ k) * ζ ^ k = 1 := fun k =>
    hnorm5 _ (by rw [← pow_mul, mul_comm, pow_mul, hζ5, one_pow])
  have horth : ∀ i j, i < 5 → j < 5 → i ≠ j → herm σ (u i) (u j) = 0 := by
    intro i j hi hj hij
    refine herm_eq_zero_of_eigen σ hE (hEu i) (hEu j) ?_
    intro h1
    have hζi : ζ ^ i ≠ 0 := pow_ne_zero _ (by rintro rfl; simp at hζ5)
    have hσi : σ (ζ ^ i) = (ζ ^ i)⁻¹ := eq_inv_of_mul_eq_one_left (hnormζ i)
    rw [hσi] at h1
    have h1' : ζ ^ i = ζ ^ j := by
      have e : ζ ^ j = ζ ^ i * ((ζ ^ i)⁻¹ * ζ ^ j) := by field_simp
      rw [e, h1, mul_one]
    exact hij (pow_inj hζ5 hζ1 hi hj h1')
  have hww : herm σ w w = 1 := by
    rw [hw, herm_single_left, map_one, one_mul]
    simp
  by_contra hcon
  push Not at hcon
  have hdiag : ∀ j ∈ Finset.range 5, herm σ (u j) (u j) = 0 := by
    intro j hj
    by_contra hne
    exact hcon j (u j) (Finset.mem_range.mp hj) hne (hEu j)
  have h0 : herm σ w w = 0 := by
    rw [← hsum, herm_sum_left']
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [herm_sum_right', Finset.sum_eq_single i]
    · exact hdiag i hi
    · intro j hj hji
      exact horth i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hji.symm
    · intro h; exact absurd hi h
  rw [hww] at h0
  exact one_ne_zero h0

@[expose] def shiftMat : Matrix (Fin 5) (Fin 5) K := Equiv.Perm.permMatrix K (finRotate 5)⁻¹

theorem shiftMat_apply (s k : Fin 5) : (shiftMat : Matrix (Fin 5) (Fin 5) K) s k =
    if k = s - 1 then 1 else 0 := by
  simp [shiftMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  exact if_congr eq_comm rfl rfl

theorem exists_frame (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0)
    (hnorm5 : ∀ x : K, x ^ 5 = 1 → σ x * x = 1)
    {ζ : K} (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1)
    {E F : Matrix (Fin 5) (Fin 5) K} (hE : IsIsom σ E) (hF : IsIsom σ F)
    (hE5 : E ^ 5 = 1) (hF5 : F ^ 5 = 1) (hEF : E * F = ζ • (F * E)) :
    ∃ (P : Matrix (Fin 5) (Fin 5) K) (lam : K), conjTr σ P * P = 1 ∧ lam ^ 5 = 1 ∧
      E * P = P * Matrix.diagonal (fun j : Fin 5 => lam * ζ ^ (j : ℕ)) ∧
        F * P = P * shiftMat := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf ζ = 5 := orderOf_eq_prime hζ5 hζ1
  have hne : ∀ k : ℕ, 0 < k → k < 5 → ζ ^ k ≠ 1 := fun k hk hk5 =>
    pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; exact hk5)
  have hz0 : ζ ≠ 0 := by rintro rfl; simp at hζ5
  obtain ⟨j, u, hj, hν, hEu⟩ := exists_eigen σ h2 hnorm5 hζ5 hζ1 hE hE5
  set ν := herm σ u u with hνdef
  have hνfix : σ ν = ν := herm_self_fixed σ hσ.invol u
  have hνinv : σ ν⁻¹ = ν⁻¹ := by rw [map_inv₀, hνfix]
  obtain ⟨c', hc'⟩ := hσ.exists_norm hνinv
  set v₀ : Fin 5 → K := c' • u with hv₀
  have hv₀n : herm σ v₀ v₀ = 1 := by
    rw [hv₀, herm_smul_left, herm_smul_right]
    calc σ c' * (c' * ν) = (σ c' * c') * ν := by ring
      _ = 1 := by rw [hc']; exact inv_mul_cancel₀ hν
  have hEv₀ : E *ᵥ v₀ = ζ ^ j • v₀ := by
    rw [hv₀, Matrix.mulVec_smul, hEu, smul_smul, smul_smul, mul_comm]
  set lam : K := ζ ^ j with hlam
  have hlam5 : lam ^ 5 = 1 := by
    rw [hlam, ← pow_mul, mul_comm, pow_mul, hζ5, one_pow]
  set vcol : ℕ → (Fin 5 → K) := fun k => F ^ k *ᵥ v₀ with hvcol
  have hEv : ∀ k : ℕ, E *ᵥ vcol k = (lam * ζ ^ k) • vcol k := by
    intro k
    simp only [hvcol]
    rw [Matrix.mulVec_mulVec, pow_mul_comm hEF, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      hEv₀, Matrix.mulVec_smul, smul_smul, mul_comm]
  have hFv : ∀ k : ℕ, F *ᵥ vcol k = vcol (k + 1) := by
    intro k
    simp only [hvcol]
    rw [Matrix.mulVec_mulVec, ← pow_succ']
  have hv5 : vcol 5 = vcol 0 := by simp [hvcol, hF5]
  have hvn : ∀ k : ℕ, herm σ (vcol k) (vcol k) = 1 := fun k => by
    simp only [hvcol]
    rw [(hF.pow σ k) v₀ v₀, hv₀n]
  have hnorm : ∀ k : ℕ, σ (lam * ζ ^ k) * (lam * ζ ^ k) = 1 := fun k =>
    hnorm5 _ (by rw [mul_pow, hlam5, ← pow_mul, mul_comm k 5, pow_mul, hζ5, one_pow, one_mul])
  have hvo : ∀ i k : ℕ, i < 5 → k < 5 → i ≠ k → herm σ (vcol i) (vcol k) = 0 := by
    intro i k hi hk hik
    refine herm_eq_zero_of_eigen σ hE (hEv i) (hEv k) ?_
    intro h1
    have hli : lam * ζ ^ i ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) (pow_ne_zero _ hz0)
    have hσi : σ (lam * ζ ^ i) = (lam * ζ ^ i)⁻¹ := eq_inv_of_mul_eq_one_left (hnorm i)
    rw [hσi] at h1
    have h1' : lam * ζ ^ i = lam * ζ ^ k := by
      have e : lam * ζ ^ k = (lam * ζ ^ i) * ((lam * ζ ^ i)⁻¹ * (lam * ζ ^ k)) := by field_simp
      rw [e, h1, mul_one]
    exact hik (pow_inj hζ5 hζ1 hi hk (mul_left_cancel₀ (pow_ne_zero _ hz0) h1'))
  refine ⟨Matrix.of fun r k => vcol (k : ℕ) r, lam, ?_, hlam5, ?_, ?_⟩
  · ext i k
    simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, Matrix.one_apply]
    show herm σ (vcol i) (vcol k) = _
    by_cases hik : i = k
    · subst hik; simp [hvn]
    · simp only [hik, ite_false]; exact hvo i k i.2 k.2 (fun h => hik (Fin.ext h))
  · ext r k
    rw [Matrix.mul_diagonal]
    have := congrFun (hEv k) r
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm] using this
  · ext r k
    have hFv' : ∀ k : Fin 5, F *ᵥ vcol (k : ℕ) = vcol ((k + 1 : Fin 5) : ℕ) := by
      intro k
      fin_cases k
      · exact hFv 0
      · exact hFv 1
      · exact hFv 2
      · exact hFv 3
      · exact (hFv 4).trans (by rw [show (4 : ℕ) + 1 = 5 from rfl, hv5]; rfl)
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have h1 := congrFun (hFv' k) r
    simp only [Matrix.mulVec, dotProduct] at h1
    simp only [Matrix.of_apply, shiftMat_apply]
    rw [h1, Finset.sum_eq_single (k + 1)]
    · simp
    · intro s _ hs
      have : ¬ k = s - 1 := by
        intro h
        apply hs
        rw [h]; simp
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h

end CFSG.RankThree.PartOne.CTP.U5Eigen

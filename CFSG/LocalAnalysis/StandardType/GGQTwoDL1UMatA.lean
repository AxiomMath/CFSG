module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2]

lemma p9uUMat_pow_three (hK : Nat.card K = 4) {x : K} (hx : x ≠ 0) : x ^ 3 = 1 := by
  classical
  letI := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h := FiniteField.pow_card (K := K) x
  rw [hcard] at h
  rw [pow_succ'] at h
  exact mul_left_cancel₀ hx (by rw [h, mul_one])

lemma p9uUMat_exists_omega (hK : Nat.card K = 4) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  classical
  letI := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hcu : Fintype.card Kˣ = 3 := by
    rw [Fintype.card_units, hcard]
  obtain ⟨u, hu⟩ :=
    Fintype.exists_ne_of_one_lt_card (α := Kˣ) (by rw [hcu]; norm_num) (1 : Kˣ)
  exact ⟨(u : K), p9uUMat_pow_three hK (Units.ne_zero u), fun h => hu (Units.ext h)⟩

lemma p9uUMat_omega_sq_add (hK : Nat.card K = 4) {ω : K}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : ω * ω + ω + 1 = 0 := by
  have hprod : (ω - 1) * (ω * ω + ω + 1) = 0 := by
    have : (ω - 1) * (ω * ω + ω + 1) = ω ^ 3 - 1 := by ring
    rw [this, hω3, sub_self]
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) hω1
  · exact h

lemma p9uUMat_cube_eq (hK : Nat.card K = 4) {ω : K}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {x : K} (hx : x ^ 3 = 1) :
    x = 1 ∨ x = ω ∨ x = ω * ω := by
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  have hx2 : x * x + x + 1 = 0 := by
    have hprod : (x - 1) * (x * x + x + 1) = 0 := by
      have : (x - 1) * (x * x + x + 1) = x ^ 3 - 1 := by ring
      rw [this, hx, sub_self]
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) hx1
    · exact h
  have hω2 := p9uUMat_omega_sq_add hK hω3 hω1
  have hsum : ω + ω * ω = 1 := by
    have h' : ω + ω * ω = -1 := by linear_combination hω2
    rwa [CharTwo.neg_eq] at h'
  have hfac : (x + ω) * (x + ω * ω) = 0 := by
    have key : (x + ω) * (x + ω * ω) = x * x + x + 1 := by
      calc (x + ω) * (x + ω * ω) = x * x + x * (ω + ω * ω) + ω ^ 3 := by ring
        _ = x * x + x + 1 := by rw [hsum, hω3]; ring
    rw [key, hx2]
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inr (Or.inl (by
      have := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at this))
  · exact Or.inr (Or.inr (by
      have := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at this))

@[expose] def p9uUMat_Allowed {n : ℕ} (J : Finset (Fin n)) (d : Fin n → K) : Prop :=
  (∀ l, d l ^ 3 = 1) ∧ (∏ l, d l = 1) ∧ (∀ a ∈ J, ∀ b ∈ J, d a = d b)

lemma p9uUMat_Allowed.mul {n : ℕ} {J : Finset (Fin n)} {d₁ d₂ : Fin n → K}
    (h₁ : p9uUMat_Allowed J d₁) (h₂ : p9uUMat_Allowed J d₂) :
    p9uUMat_Allowed J (fun l => d₁ l * d₂ l) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l; rw [mul_pow, h₁.1 l, h₂.1 l, mul_one]
  · rw [Finset.prod_mul_distrib, h₁.2.1, h₂.2.1, mul_one]
  · intro a ha b hb
    show d₁ a * d₂ a = d₁ b * d₂ b
    rw [h₁.2.2 a ha b hb, h₂.2.2 a ha b hb]

def p9uUMat_onJ {n : ℕ} (J : Finset (Fin n)) (w : K) : Fin n → K :=
  fun l => if l ∈ J then w else 1

lemma p9uUMat_onJ_apply_mem {n : ℕ} {J : Finset (Fin n)} {w : K} {a : Fin n}
    (ha : a ∈ J) : p9uUMat_onJ J w a = w := by
  simp [p9uUMat_onJ, ha]

lemma p9uUMat_onJ_apply_notMem {n : ℕ} {J : Finset (Fin n)} {w : K} {a : Fin n}
    (ha : a ∉ J) : p9uUMat_onJ J w a = 1 := by
  simp [p9uUMat_onJ, ha]

lemma p9uUMat_onJ_prod {n : ℕ} (J : Finset (Fin n)) (w : K) :
    ∏ l, p9uUMat_onJ J w l = w ^ J.card := by
  change ∏ l : Fin n, (if l ∈ J then w else 1) = w ^ J.card
  rw [Finset.prod_ite_mem_eq, Finset.prod_const]

lemma p9uUMat_onJ_allowed {n : ℕ} {J : Finset (Fin n)} (hJ : J.card = 0 ∨ J.card = 3)
    {w : K} (hw : w ^ 3 = 1) : p9uUMat_Allowed J (p9uUMat_onJ J w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l; by_cases hl : l ∈ J <;> simp [p9uUMat_onJ, hl, hw]
  · rw [p9uUMat_onJ_prod]
    rcases hJ with h | h <;> rw [h] <;> simp [hw]
  · intro a ha b hb; rw [p9uUMat_onJ_apply_mem ha, p9uUMat_onJ_apply_mem hb]

def p9uUMat_two {n : ℕ} (i j : Fin n) (u v : K) : Fin n → K :=
  fun l => if l = i then u else if l = j then v else 1

lemma p9uUMat_two_apply_i {n : ℕ} (i j : Fin n) (u v : K) :
    p9uUMat_two i j u v i = u := by
  simp [p9uUMat_two]

lemma p9uUMat_two_apply_j {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u v : K) :
    p9uUMat_two i j u v j = v := by
  simp [p9uUMat_two, Ne.symm hij]

lemma p9uUMat_two_apply_of_ne {n : ℕ} {i j x : Fin n} (hxi : x ≠ i) (hxj : x ≠ j)
    (u v : K) : p9uUMat_two i j u v x = 1 := by
  simp [p9uUMat_two, hxi, hxj]

lemma p9uUMat_two_prod {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u v : K) :
    ∏ l, p9uUMat_two i j u v l = u * v := by
  have hpt : p9uUMat_two i j u v =
      fun l => (if l = i then u else 1) * (if l = j then v else 1) := by
    funext l
    change (if l = i then u else if l = j then v else 1) =
      (if l = i then u else 1) * (if l = j then v else 1)
    by_cases hli : l = i
    · subst hli; simp [hij]
    · by_cases hlj : l = j
      · subst hlj; simp [Ne.symm hij]
      · simp [hli, hlj]
  have h1 : ∏ l : Fin n, (if l = i then u else 1) = u := by
    simpa using (Finset.prod_eq_single (s := Finset.univ)
      (f := fun l : Fin n => if l = i then u else 1) i
      (fun b _ hb => by simp [hb]) (fun _ => by simp))
  have h2 : ∏ l : Fin n, (if l = j then v else 1) = v := by
    simpa using (Finset.prod_eq_single (s := Finset.univ)
      (f := fun l : Fin n => if l = j then v else 1) j
      (fun b _ hb => by simp [hb]) (fun _ => by simp))
  rw [hpt, Finset.prod_mul_distrib, h1, h2]

lemma p9uUMat_two_allowed {n : ℕ} {J : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (hi : i ∉ J) (hj : j ∉ J) {u v : K} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (huv : u * v = 1) :
    p9uUMat_Allowed J (p9uUMat_two i j u v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l
    by_cases hli : l = i
    · subst hli; rw [p9uUMat_two_apply_i, hu]
    · by_cases hlj : l = j
      · subst hlj; rw [p9uUMat_two_apply_j hij, hv]
      · rw [p9uUMat_two_apply_of_ne hli hlj]; norm_num
  · rw [p9uUMat_two_prod hij, huv]
  · intro a ha b hb
    have hai : a ≠ i := fun h => hi (by rwa [h] at ha)
    have haj : a ≠ j := fun h => hj (by rwa [h] at ha)
    have hbi : b ≠ i := fun h => hi (by rwa [h] at hb)
    have hbj : b ≠ j := fun h => hj (by rwa [h] at hb)
    rw [p9uUMat_two_apply_of_ne hai haj, p9uUMat_two_apply_of_ne hbi hbj]

lemma p9uUMat_omega_ne_zero {ω : K} (hω3 : ω ^ 3 = 1) : ω ≠ 0 := by
  intro h
  rw [h, zero_pow (by norm_num : 3 ≠ 0)] at hω3
  exact one_ne_zero hω3.symm

lemma p9uUMat_omega_sq_ne_one {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ω * ω ≠ 1 := by
  intro h
  apply hω1
  calc ω = ω * 1 := (mul_one ω).symm
    _ = ω * (ω * ω) := by rw [← h]
    _ = ω ^ 3 := by ring
    _ = 1 := hω3

lemma p9uUMat_omega_ne_sq {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ω ≠ ω * ω := by
  intro h
  have hh := congrArg (fun t : K => ω * t) h
  rw [show ω * (ω * ω) = ω ^ 3 by ring, hω3] at hh
  exact p9uUMat_omega_sq_ne_one hω3 hω1 hh

lemma p9uUMat_exists_two_ne {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    ∃ k l : Fin n, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j := by
  have h2 : 2 ≤ (Finset.univ \ ({i, j} : Finset (Fin n))).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
    omega
  obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq h2
  obtain ⟨k, l, hkl, hteq⟩ := Finset.card_eq_two.mp htcard
  subst hteq
  have hkC : k ∉ ({i, j} : Finset (Fin n)) := (Finset.mem_sdiff.mp (ht (by simp))).2
  have hlC : l ∉ ({i, j} : Finset (Fin n)) := (Finset.mem_sdiff.mp (ht (by simp))).2
  refine ⟨k, l, hkl, ?_, ?_, ?_, ?_⟩
  · intro h; exact hkC (by rw [h]; exact Finset.mem_insert_self i {j})
  · intro h; exact hkC (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
  · intro h; exact hlC (by rw [h]; exact Finset.mem_insert_self i {j})
  · intro h; exact hlC (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j))

lemma p9uUMat_coeff_one {n : ℕ} (hK : Nat.card K = 4) (hn : 4 ≤ n)
    {i j : Fin n} (hij : i ≠ j) {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {τ : K ≃+* K} {π : Equiv.Perm (Fin n)} {c : K} (hc3 : c ^ 3 = 1)
    (hrel : ∀ m, τ (p9uUMat_two i j ω (ω * ω) m) =
      c * p9uUMat_two i j ω (ω * ω) (π m)) : c = 1 := by
  have hω0 : ω ≠ 0 := p9uUMat_omega_ne_zero hω3
  have hω2_0 : ω * ω ≠ 0 := mul_ne_zero hω0 hω0
  have hω_mul : ω * (ω * ω) = 1 := by
    calc ω * (ω * ω) = ω ^ 3 := by ring
      _ = 1 := hω3
  have hω2_mul : (ω * ω) * ω = 1 := by rw [mul_comm]; exact hω_mul
  obtain ⟨k, l, hkl, hki, hkj, hli, hlj⟩ := p9uUMat_exists_two_ne hn i j hij
  have hdk : p9uUMat_two i j ω (ω * ω) k = 1 := p9uUMat_two_apply_of_ne hki hkj _ _
  have hdl : p9uUMat_two i j ω (ω * ω) l = 1 := p9uUMat_two_apply_of_ne hli hlj _ _
  have keyj : ∀ m : Fin n, p9uUMat_two i j ω (ω * ω) m = ω * ω → m = j := by
    intro m hm
    by_cases hmj : m = j
    · exact hmj
    · by_cases hmi : m = i
      · subst hmi
        rw [p9uUMat_two_apply_i] at hm
        exact absurd hm (p9uUMat_omega_ne_sq hω3 hω1)
      · rw [p9uUMat_two_apply_of_ne hmi hmj] at hm
        exact absurd hm.symm (p9uUMat_omega_sq_ne_one hω3 hω1)
  have keyi : ∀ m : Fin n, p9uUMat_two i j ω (ω * ω) m = ω → m = i := by
    intro m hm
    by_cases hmi : m = i
    · exact hmi
    · by_cases hmj : m = j
      · subst hmj
        rw [p9uUMat_two_apply_j hij] at hm
        exact absurd hm.symm (p9uUMat_omega_ne_sq hω3 hω1)
      · rw [p9uUMat_two_apply_of_ne hmi hmj] at hm
        exact absurd hm.symm hω1
  rcases p9uUMat_cube_eq hK hω3 hω1 hc3 with hc | hc | hc
  · exact hc
  · exfalso
    have hkω : p9uUMat_two i j ω (ω * ω) (π k) = ω * ω := by
      have h := hrel k
      rw [hdk, map_one, hc] at h
      have : ω * p9uUMat_two i j ω (ω * ω) (π k) = ω * (ω * ω) := by rw [← h, hω_mul]
      exact mul_left_cancel₀ hω0 this
    have hlω : p9uUMat_two i j ω (ω * ω) (π l) = ω * ω := by
      have h := hrel l
      rw [hdl, map_one, hc] at h
      have : ω * p9uUMat_two i j ω (ω * ω) (π l) = ω * (ω * ω) := by rw [← h, hω_mul]
      exact mul_left_cancel₀ hω0 this
    exact hkl (π.injective ((keyj (π k) hkω).trans (keyj (π l) hlω).symm))
  · exfalso
    have hkω : p9uUMat_two i j ω (ω * ω) (π k) = ω := by
      have h := hrel k
      rw [hdk, map_one, hc] at h
      have : (ω * ω) * p9uUMat_two i j ω (ω * ω) (π k) = (ω * ω) * ω := by
        rw [← h, hω2_mul]
      exact mul_left_cancel₀ hω2_0 this
    have hlω : p9uUMat_two i j ω (ω * ω) (π l) = ω := by
      have h := hrel l
      rw [hdl, map_one, hc] at h
      have : (ω * ω) * p9uUMat_two i j ω (ω * ω) (π l) = (ω * ω) * ω := by
        rw [← h, hω2_mul]
      exact mul_left_cancel₀ hω2_0 this
    exact hkl (π.injective ((keyi (π k) hkω).trans (keyi (π l) hlω).symm))

lemma p9uUMat_entry {n : ℕ} {g : GL (Fin n) K} {τ : K ≃+* K} {d : Fin n → K}
    {c : K}
    (h : (g : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun l => τ (d l)) =
      c • (Matrix.diagonal d * (g : Matrix (Fin n) (Fin n) K))) (x y : Fin n) :
    (g : Matrix (Fin n) (Fin n) K) x y * τ (d y) =
      c * d x * (g : Matrix (Fin n) (Fin n) K) x y := by
  have hxy := congrFun (congrFun h x) y
  simpa [Matrix.smul_apply, mul_assoc] using hxy

lemma p9uUMat_exists_perm {n : ℕ} (g : GL (Fin n) K) :
    ∃ π : Equiv.Perm (Fin n), ∀ a, (g : Matrix (Fin n) (Fin n) K) (π a) a ≠ 0 := by
  have hdet : (g : Matrix (Fin n) (Fin n) K).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  rw [Matrix.det_apply] at hdet
  have hdet' : ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
      Equiv.Perm.sign σ • ∏ i, (g : Matrix (Fin n) (Fin n) K) (σ i) i ≠ 0 := by
    simpa using hdet
  obtain ⟨π, -, hπ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet'
  refine ⟨π, fun a => ?_⟩
  have hprod : ∏ i, (g : Matrix (Fin n) (Fin n) K) (π i) i ≠ 0 := by
    intro hp
    exact hπ (by rw [hp, smul_zero])
  have hprod' : ∏ i ∈ (Finset.univ : Finset (Fin n)),
      (g : Matrix (Fin n) (Fin n) K) (π i) i ≠ 0 := by simpa using hprod
  exact (Finset.prod_ne_zero_iff.mp hprod') a (Finset.mem_univ a)

lemma p9uUMat_isUnitary_mul {n : ℕ} {g₁ g₂ : GL (Fin n) K}
    (h₁ : ggIsUnitaryMat (p := 2) (f := 1) g₁) (h₂ : ggIsUnitaryMat (p := 2) (f := 1) g₂) :
    ggIsUnitaryMat (p := 2) (f := 1) (g₁ * g₂) := by
  unfold ggIsUnitaryMat at h₁ h₂ ⊢
  rw [Units.val_mul, conjTr_mul]
  calc conjTr (unitaryInvolution K 2 1) (g₂ : Matrix (Fin n) (Fin n) K) *
        conjTr (unitaryInvolution K 2 1) (g₁ : Matrix (Fin n) (Fin n) K) *
          ((g₁ : Matrix (Fin n) (Fin n) K) * (g₂ : Matrix (Fin n) (Fin n) K))
      = conjTr (unitaryInvolution K 2 1) (g₂ : Matrix (Fin n) (Fin n) K) *
          (conjTr (unitaryInvolution K 2 1) (g₁ : Matrix (Fin n) (Fin n) K) *
            (g₁ : Matrix (Fin n) (Fin n) K)) *
          (g₂ : Matrix (Fin n) (Fin n) K) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h₁, Matrix.mul_one, h₂]

lemma p9uUMat_isUnitary_pow {n : ℕ} {g : GL (Fin n) K}
    (hg : ggIsUnitaryMat (p := 2) (f := 1) g) (m : ℕ) :
    ggIsUnitaryMat (p := 2) (f := 1) (g ^ m) := by
  induction m with
  | zero =>
      unfold ggIsUnitaryMat
      rw [pow_zero, Units.val_one, conjTr_one, Matrix.one_mul]
  | succ m ih => rw [pow_succ]; exact p9uUMat_isUnitary_mul ih hg

lemma p9uUMat_unitary_scalar_cube {n : ℕ} (hn : 0 < n) {c : K}
    (h : conjTr (unitaryInvolution K 2 1) (c • (1 : Matrix (Fin n) (Fin n) K)) *
      (c • (1 : Matrix (Fin n) (Fin n) K)) = 1) : c ^ 3 = 1 := by
  have h00 := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
  simp [conjTr, Matrix.mul_apply, Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply,
    Matrix.map_apply, Matrix.transpose_apply, Matrix.one_apply] at h00
  rw [frobenius_def] at h00
  simpa [pow_succ] using h00

lemma p9uUMat_pow_two_pow {c : K} (h0 : c ≠ 0) (h3 : c ^ 3 = 1) (k : ℕ) :
    c ^ (2 ^ k) = if Even k then c else c⁻¹ := by
  have hsq : c ^ 2 = c⁻¹ :=
    (inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h3])).symm
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih]
    by_cases hk : Even k
    · rw [if_pos hk, if_neg (fun h => (Nat.even_add_one.mp h) hk), hsq]
    · rw [if_neg hk, if_pos (Nat.even_add_one.mpr hk), inv_pow, hsq, inv_inv]

lemma p9uUMat_scalar_root {c₀ : K} (hc0 : c₀ ^ 3 = 1) (k : ℕ) :
    ∃ c : K, c ^ 3 = 1 ∧ c ^ (2 ^ k) = c₀⁻¹ := by
  have h0 : c₀ ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : 3 ≠ 0)] at hc0
    exact one_ne_zero hc0.symm
  refine ⟨if Even k then c₀⁻¹ else c₀, ?_, ?_⟩
  · split_ifs with hk
    · rw [inv_pow, hc0, inv_one]
    · exact hc0
  · split_ifs with hk
    · rw [inv_pow, p9uUMat_pow_two_pow h0 hc0 k, if_pos hk]
    · rw [p9uUMat_pow_two_pow h0 hc0 k, if_neg hk]

lemma p9uUMat_smul_pow {n : ℕ} (c : K) (G : Matrix (Fin n) (Fin n) K) (m : ℕ) :
    (c • G) ^ m = c ^ m • G ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, pow_succ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ]

lemma p9uUMat_det_conjTr {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (conjTr (unitaryInvolution K 2 1) A).det = unitaryInvolution K 2 1 A.det := by
  rw [conjTr, Matrix.det_transpose]
  exact (RingEquiv.map_det (unitaryInvolution K 2 1) A).symm

lemma p9uUMat_diag_of_col_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) K} {i : Fin n}
    (h : ∀ k, k ≠ i → A k i = 0) (m : ℕ) : (A ^ m) i i = (A i i) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [ih, pow_succ]
    · intro k _ hk; rw [h k hk, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi

lemma p9uUMat_entry_diag_of_col_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) K} {i : Fin n}
    (h : ∀ k, k ≠ i → A k i = 0) :
    (conjTr (unitaryInvolution K 2 1) A * A) i i = unitaryInvolution K 2 1 (A i i) * A i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [conjTr, Matrix.transpose_apply, Matrix.map_apply]
  · intro k _ hk; rw [h k hk, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi


end CFSG.StandardType.QTwo

end

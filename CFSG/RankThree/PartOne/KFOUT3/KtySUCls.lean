module

public import CFSG.RankThree.PartOne.KF.SUGram

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary Matrix

section Cls

variable {K : Type} [Field K]

@[expose] def rhoEnt (σ : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) (c c' : Fin 5) : K :=
  if c = 0 ∧ c' = 0 then A 0 0 else if c = 0 ∧ c' = 1 then A 0 1 else
  if c = 1 ∧ c' = 0 then A 1 0 else if c = 1 ∧ c' = 1 then A 1 1 else
  if c = 2 ∧ c' = 2 then σ (A 0 0) else if c = 2 ∧ c' = 3 then σ (A 0 1) else
  if c = 3 ∧ c' = 2 then σ (A 1 0) else if c = 3 ∧ c' = 3 then σ (A 1 1) else
  if c = 4 ∧ c' = 4 then 1 else 0

theorem rhoEnt_mul (σ : K ≃+* K) (A B : Matrix (Fin 2) (Fin 2) K) (c c' : Fin 5) :
    ∑ d : Fin 5, rhoEnt σ A c d * rhoEnt σ B d c' = rhoEnt σ (A * B) c c' := by
  fin_cases c <;> fin_cases c' <;>
    simp [Fin.sum_univ_five, rhoEnt, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]

theorem rhoEnt_one (σ : K ≃+* K) (c c' : Fin 5) :
    rhoEnt σ (1 : Matrix (Fin 2) (Fin 2) K) c c' = if c = c' then 1 else 0 := by
  fin_cases c <;> fin_cases c' <;> simp [rhoEnt]

theorem rhoEnt_gram [CharP K 2] (σ : K ≃+* K) (hσ : ∀ x, σ (σ x) = x) (A : Matrix (Fin 2) (Fin 2) K)
    (hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1) (c₁ c₂ : Fin 5) :
    ∑ d : Fin 5, σ (rhoEnt σ A d c₁) * rhoEnt σ A (d8Rho d) c₂ =
      if c₂ = d8Rho c₁ then 1 else 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdσ : σ (A 0 0) * σ (A 1 1) - σ (A 0 1) * σ (A 1 0) = 1 := by
    have := congrArg σ hdet
    simpa [map_sub, map_mul] using this
  fin_cases c₁ <;> fin_cases c₂ <;>
    simp [Fin.sum_univ_five, rhoEnt, d8Rho, hσ] <;>
    first
    | linear_combination hdσ + (σ (A 0 1) * σ (A 1 0)) * h2
    | linear_combination hdet + (A 0 1 * A 1 0) * h2
    | linear_combination (A 0 0 * A 1 0) * h2
    | linear_combination (σ (A 0 0) * σ (A 1 0)) * h2
    | linear_combination (A 0 1 * A 1 1) * h2
    | linear_combination (σ (A 0 1) * σ (A 1 1)) * h2

theorem rhoEnt_right_four (σ : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) {c : Fin 5} (hc : c ≠ 4) :
    rhoEnt σ A c 4 = 0 := by
  fin_cases c <;> simp_all [rhoEnt]

theorem rhoEnt_left_four (σ : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) {c : Fin 5} (hc : c ≠ 4) :
    rhoEnt σ A 4 c = 0 := by
  fin_cases c <;> simp_all [rhoEnt]

theorem cls_missing_four : ∀ d : Fin 5, (∀ i : Fin 4, d8Cls 4 i ≠ d) →
    d = 4 ∧ ∀ i : Fin 4, d8Cls 4 i ≠ 4 := by
  decide

theorem cls_missing_five : ∀ d : Fin 5, (∀ i : Fin 5, d8Cls 5 i ≠ d) →
    d = 4 ∧ ∀ i : Fin 5, d8Cls 5 i ≠ 4 := by
  decide

variable {n : ℕ} [NeZero n]

@[expose] def rhoMat (n : ℕ) [NeZero n] (σ : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => rhoEnt σ A (d8Cls n i) (d8Cls n j)

theorem cls_missing (hn : n = 4 ∨ n = 5) :
    ∀ d : Fin 5, d ∉ Set.range (d8Cls n) → d = 4 ∧ ∀ i, d8Cls n i ≠ 4 := by
  intro d hd
  rw [Set.mem_range, not_exists] at hd
  rcases hn with rfl | rfl
  · exact cls_missing_four d hd
  · exact cls_missing_five d hd

theorem cls_injective (hc : D8Comb n) : Function.Injective (d8Cls n) := fun i j h =>
  by_contra fun hne => hc.cls_inj i j hne h

theorem sum_cls (hc : D8Comb n) (G : Fin 5 → K)
    (hG : ∀ d, d ∉ Set.range (d8Cls n) → G d = 0) :
    ∑ k : Fin n, G (d8Cls n k) = ∑ d : Fin 5, G d := by
  rw [← Finset.sum_image (s := Finset.univ) (g := d8Cls n) (f := G)
    (fun x _ y _ h => cls_injective hc h)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro d _ hd
  apply hG
  rintro ⟨i, hi⟩
  exact hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)

theorem rhoMat_mul (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K)
    (A B : Matrix (Fin 2) (Fin 2) K) :
    rhoMat n σ A * rhoMat n σ B = rhoMat n σ (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, rhoMat, Matrix.of_apply]
  rw [sum_cls hc (fun d => rhoEnt σ A (d8Cls n i) d * rhoEnt σ B d (d8Cls n j))]
  · exact rhoEnt_mul σ A B _ _
  · intro d hd
    obtain ⟨rfl, h4⟩ := cls_missing hn d hd
    simp [rhoEnt_right_four σ A (h4 i)]

theorem rhoMat_one (hc : D8Comb n) (σ : K ≃+* K) :
    rhoMat n σ (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  simp [rhoMat, rhoEnt_one, Matrix.one_apply, (cls_injective hc).eq_iff]

omit [NeZero n] in
theorem gram_apply (σ : K ≃+* K) (R : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (conjTr σ R * antidiag n * R : Matrix (Fin n) (Fin n) K) i j =
      ∑ k, σ (R k i) * R (Fin.rev k) j := by
  simp only [Matrix.mul_apply, conjTr, antidiag, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.map_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [ite_mul]

theorem rhoMat_gram [CharP K 2] (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K)
    (hσ : ∀ x, σ (σ x) = x) (A : Matrix (Fin 2) (Fin 2) K)
    (hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1) :
    conjTr σ (rhoMat n σ A) * antidiag n * rhoMat n σ A = antidiag n := by
  ext i j
  rw [gram_apply]
  simp only [antidiag, Matrix.of_apply]
  have h1 : ∀ k : Fin n, σ (rhoMat n σ A k i) * rhoMat n σ A (Fin.rev k) j =
      (fun d : Fin 5 => σ (rhoEnt σ A d (d8Cls n i)) * rhoEnt σ A (d8Rho d) (d8Cls n j))
        (d8Cls n k) := by
    intro k
    simp [rhoMat, hc.cls_rev]
  have h2 := sum_cls hc (fun d : Fin 5 => σ (rhoEnt σ A d (d8Cls n i)) *
    rhoEnt σ A (d8Rho d) (d8Cls n j)) (by
      intro d hd
      obtain ⟨rfl, h4⟩ := cls_missing hn d hd
      simp [rhoEnt_left_four σ A (h4 i)])
  rw [Finset.sum_congr rfl fun k _ => h1 k, h2, rhoEnt_gram σ hσ A hdet]
  have : d8Cls n j = d8Rho (d8Cls n i) ↔ j = Fin.rev i := by
    rw [← hc.cls_rev, (cls_injective hc).eq_iff]
  simp only [this]

theorem rhoEnt_comm_aa (σ : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) (a : Kˣ) (c c' : Fin 5) :
    rhoEnt σ A c c' * (d8EvU c' a a : K) = (d8EvU c a a : K) * rhoEnt σ A c c' := by
  fin_cases c <;> fin_cases c' <;> simp [rhoEnt, d8EvU, mul_comm]

end Cls

section Block

variable {K : Type} [Field K] {n k : ℕ}

theorem entry_eq_zero_of_commute {d : Fin n → K} {m : Matrix (Fin n) (Fin n) K}
    (h : m * Matrix.diagonal d = Matrix.diagonal d * m) {i j : Fin n} (hij : d i ≠ d j) :
    m i j = 0 := by
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  by_contra hne
  apply hij
  have : m i j * d j = m i j * d i := by rw [h1]; ring
  exact (mul_left_cancel₀ hne this).symm

theorem submatrix_mul_of_vanish {e : Fin k → Fin n} (he : Function.Injective e)
    {m m' : Matrix (Fin n) (Fin n) K} (hm : ∀ a j, j ∉ Set.range e → m (e a) j = 0) :
    (m * m').submatrix e e = m.submatrix e e * m'.submatrix e e := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_image (s := Finset.univ) (g := e)
    (f := fun l => m (e a) l * m' l (e b)) (fun x _ y _ h => he h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro l _ hl
  rw [hm a l (fun ⟨c, hc⟩ => hl (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩)), zero_mul]

@[expose] noncomputable def blkHom (e : Fin k → Fin n) (he : Function.Injective e)
    (C : Subgroup (GL (Fin n) K))
    (hC : ∀ m ∈ C, ∀ a j, j ∉ Set.range e → ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (e a) j = 0) :
    ↥C →* GL (Fin k) K :=
  ({ toFun := fun m => ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix e e
     map_one' := by
       show ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix e e = 1
       rw [Units.val_one]
       exact Matrix.submatrix_one e he
     map_mul' := fun m m' => by
       show ((m * m' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix e e = _
       rw [Units.val_mul]
       exact submatrix_mul_of_vanish he (hC m m.2) } : ↥C →* Matrix (Fin k) (Fin k) K).toHomUnits

theorem blkHom_val (e : Fin k → Fin n) (he : Function.Injective e) (C : Subgroup (GL (Fin n) K))
    (hC : ∀ m ∈ C, ∀ a j, j ∉ Set.range e → ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (e a) j = 0)
    (m : ↥C) :
    ((blkHom e he C hC m : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix e e := rfl

end Block

section Facts

variable {K : Type} [Field K] {n : ℕ} [NeZero n]

theorem cls_zero : d8Cls n 0 = 0 := by simp [d8Cls]

theorem cls_one (hc : D8Comb n) : d8Cls n 1 = 1 := by simp [d8Cls, hc.one_ne_zero]

theorem cls_rev_zero (hc : D8Comb n) : d8Cls n (Fin.rev 0) = 3 := by
  rw [hc.cls_rev, cls_zero]; rfl

theorem cls_rev_one (hc : D8Comb n) : d8Cls n (Fin.rev 1) = 2 := by
  rw [hc.cls_rev, cls_one hc]; rfl

theorem index_kinds (i : Fin n) :
    i = 0 ∨ i = 1 ∨ i = Fin.rev 1 ∨ i = Fin.rev 0 ∨ d8Cls n i = 4 := by
  unfold d8Cls
  split_ifs with h0 h1 h2 h3
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h2))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

@[expose] def gp (n : ℕ) [NeZero n] (i : Fin n) : ℕ := (d8Cls n i).val / 2

theorem gp_zero : gp n 0 = 0 := by simp [gp, cls_zero]

theorem gp_one (hc : D8Comb n) : gp n 1 = 0 := by simp [gp, cls_one hc]

theorem gp_rev_one (hc : D8Comb n) : gp n (Fin.rev 1) = 1 := by simp [gp, cls_rev_one hc]

theorem gp_rev_zero (hc : D8Comb n) : gp n (Fin.rev 0) = 1 := by simp [gp, cls_rev_zero hc]

theorem gp_middle {i : Fin n} (h : d8Cls n i = 4) : gp n i = 2 := by simp [gp, h]

theorem evU_aa_eq_iff {a : Kˣ} (ha1 : a ≠ 1) (ha2 : a⁻¹ ≠ a) (c c' : Fin 5) :
    d8EvU c a a = d8EvU c' a a ↔ c.val / 2 = c'.val / 2 := by
  have ha3 : a⁻¹ ≠ 1 := inv_ne_one.mpr ha1
  fin_cases c <;> fin_cases c' <;> simp [d8EvU, ha1, ha2, ha3, ha1.symm, ha2.symm, ha3.symm]

theorem vanish_aa {a : Kˣ} (ha1 : a ≠ 1) (ha2 : a⁻¹ ≠ a) {m : Matrix (Fin n) (Fin n) K}
    (h : m * Matrix.diagonal (fun i => (dvecN n a a i : K)) =
      Matrix.diagonal (fun i => (dvecN n a a i : K)) * m)
    {i j : Fin n} (hij : gp n i ≠ gp n j) : m i j = 0 := by
  apply entry_eq_zero_of_commute h
  intro heq
  apply hij
  have : d8EvU (d8Cls n i) a a = d8EvU (d8Cls n j) a a := Units.ext heq
  exact (evU_aa_eq_iff ha1 ha2 _ _).mp this

omit [NeZero n] in
theorem sum_eq_pair {f : Fin n → K} {i j : Fin n} (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → f k = 0) : ∑ k, f k = f i + f j := by
  rw [← Finset.sum_pair hij]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  apply h <;> intro e <;> simp [e] at hk

theorem gp_eq_zero_iff (hc : D8Comb n) {j : Fin n} : gp n j = 0 ↔ j = 0 ∨ j = 1 := by
  constructor
  · intro h
    rcases index_kinds j with h0 | h0 | h0 | h0 | h0
    · exact Or.inl h0
    · exact Or.inr h0
    · rw [h0, gp_rev_one hc] at h; omega
    · rw [h0, gp_rev_zero hc] at h; omega
    · rw [gp_middle h0] at h; omega
  · rintro (h | h)
    · rw [h]; exact gp_zero
    · rw [h]; exact gp_one hc

theorem gp_eq_two_iff {j : Fin n} : gp n j = 2 ↔ d8Cls n j = 4 := by
  constructor
  · intro h
    have : (d8Cls n j).val / 2 = 2 := h
    have h5 : (d8Cls n j).val < 5 := (d8Cls n j).isLt
    have : (d8Cls n j).val = 4 := by omega
    exact Fin.ext this
  · exact gp_middle

omit [NeZero n] in
theorem comm_matrix {d : Fin n → Kˣ} {x : GL (Fin n) K}
    (hx : x * diagU d = diagU d * x) :
    (x : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun i => (d i : K)) =
      Matrix.diagonal (fun i => (d i : K)) * (x : Matrix (Fin n) (Fin n) K) := by
  have := congrArg Units.val hx
  simpa [diagU_val] using this

@[expose] def gq (c : Fin 5) : ℕ := if c = 1 then 1 else if c = 2 then 2 else 0

theorem evU_1b_eq_iff {b : Kˣ} (hb1 : b ≠ 1) (hb2 : b⁻¹ ≠ b) (c c' : Fin 5) :
    d8EvU c 1 b = d8EvU c' 1 b ↔ gq c = gq c' := by
  have hb3 : b⁻¹ ≠ 1 := inv_ne_one.mpr hb1
  fin_cases c <;> fin_cases c' <;>
    simp [d8EvU, gq, hb1, hb2, hb3, hb1.symm, hb2.symm, hb3.symm]

theorem vanish_1b {b : Kˣ} (hb1 : b ≠ 1) (hb2 : b⁻¹ ≠ b) {m : Matrix (Fin n) (Fin n) K}
    (h : m * Matrix.diagonal (fun i => (dvecN n 1 b i : K)) =
      Matrix.diagonal (fun i => (dvecN n 1 b i : K)) * m)
    {i j : Fin n} (hij : gq (d8Cls n i) ≠ gq (d8Cls n j)) : m i j = 0 := by
  apply entry_eq_zero_of_commute h
  intro heq
  apply hij
  have : d8EvU (d8Cls n i) 1 b = d8EvU (d8Cls n j) 1 b := Units.ext heq
  exact (evU_1b_eq_iff hb1 hb2 _ _).mp this

theorem gq_cls_one (hc : D8Comb n) : gq (d8Cls n 1) = 1 := by simp [cls_one hc, gq]

theorem gq_cls_rev_one (hc : D8Comb n) : gq (d8Cls n (Fin.rev 1)) = 2 := by
  simp [cls_rev_one hc, gq]

theorem gq_cls_eq_one_iff (hc : D8Comb n) {j : Fin n} : gq (d8Cls n j) = 1 ↔ j = 1 := by
  constructor
  · intro h
    have : d8Cls n j = 1 := by
      generalize d8Cls n j = c at h
      fin_cases c <;> simp_all [gq]
    rw [← cls_one hc] at this
    exact cls_injective hc this
  · rintro rfl; exact gq_cls_one hc

theorem gq_cls_eq_two_iff (hc : D8Comb n) {j : Fin n} :
    gq (d8Cls n j) = 2 ↔ j = Fin.rev 1 := by
  constructor
  · intro h
    have : d8Cls n j = 2 := by
      generalize d8Cls n j = c at h
      fin_cases c <;> simp_all [gq]
    rw [← cls_rev_one hc] at this
    exact cls_injective hc this
  · rintro rfl; exact gq_cls_rev_one hc

end Facts

end CFSG.RankThree.PartOne.KFOUT3

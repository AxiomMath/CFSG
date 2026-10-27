module

public import CFSG.RankThree.GF2n.Smith81.S81NTk

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open scoped commutatorElement

variable {K : Type*} [Field K]

@[expose] noncomputable def diagGL (d : Fin 6 → K) (hd : ∀ i, d i ≠ 0) : GL (Fin 6) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d)
    (by simp [Matrix.det_diagonal, Finset.prod_ne_zero_iff, hd])

theorem diagGL_val (d : Fin 6 → K) (hd : ∀ i, d i ≠ 0) :
    (diagGL d hd : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal d := rfl

theorem det_diagGL (d : Fin 6 → K) (hd : ∀ i, d i ≠ 0) :
    (diagGL d hd : Matrix (Fin 6) (Fin 6) K).det = ∏ i, d i := by
  rw [diagGL_val, Matrix.det_diagonal]

theorem det_transvGL (i j : Fin 6) (hij : i ≠ j) (c : K) :
    (transvGL K i j hij c : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  rw [transvGL_val]
  exact Matrix.det_transvection_of_ne i j hij c

private theorem diagonal_mul_single_aux (d : Fin 6 → K) (i j : Fin 6) (c : K) :
    Matrix.diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  by_cases ha : i = a <;> by_cases hb : j = b <;> simp [ha, hb]

private theorem single_mul_diagonal_aux (d : Fin 6 → K) (i j : Fin 6) (c : K) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.single i j (c * d j) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  by_cases ha : i = a <;> by_cases hb : j = b <;> simp [ha, hb]

private theorem transvection_comm_aux {i j k l : Fin 6} (hjk : j ≠ k) (hli : l ≠ i) (a b : K) :
    Matrix.transvection i j a * Matrix.transvection k l b =
      Matrix.transvection k l b * Matrix.transvection i j a := by
  simp only [Matrix.transvection, add_mul, mul_add, one_mul, mul_one, add_zero,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk, Matrix.single_mul_single_of_ne _ _ _ _ hli]
  abel

private theorem steinberg_aux {i j k : Fin 6} (hjk : j ≠ k) (hik : i ≠ k) (a b : K) :
    Matrix.transvection i j a * Matrix.transvection j k b =
      Matrix.transvection i k (a * b) * Matrix.transvection j k b * Matrix.transvection i j a := by
  have hkj : k ≠ j := hjk.symm
  have hki : k ≠ i := hik.symm
  simp only [Matrix.transvection, add_mul, mul_add, one_mul, mul_one, add_zero, zero_add,
    zero_mul, mul_zero, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hkj, Matrix.single_mul_single_of_ne _ _ _ _ hki]
  abel

private theorem diag_transvection_aux (d : Fin 6 → K) (hd : ∀ m, d m ≠ 0) (i j : Fin 6)
    (hij : i ≠ j) (c : K) :
    Matrix.diagonal d * Matrix.transvection i j c =
      Matrix.transvection i j ((d i / d j - 1) * c) * Matrix.transvection i j c *
        Matrix.diagonal d := by
  have hji : j ≠ i := hij.symm
  have key : Matrix.single i j (d i * c) =
      Matrix.single i j (c * d j) + Matrix.single i j ((d i / d j - 1) * c * d j) := by
    rw [← Matrix.single_add]
    congr 1
    have h := div_mul_cancel₀ (d i) (hd j)
    linear_combination (-c) * h
  simp only [Matrix.transvection, mul_add, add_mul, one_mul, mul_one, add_zero,
    diagonal_mul_single_aux, single_mul_diagonal_aux, Matrix.single_mul_single_of_ne _ _ _ _ hji]
  rw [key]
  abel

private theorem comm_eq_of_mul_eq {G : Type*} [Group G] {g x y : G} (h : g * x = y * x * g) :
    ⁅g, x⁆ = y := by
  rw [commutatorElement_def, h]
  group

private theorem comm_mul_of_comm {G : Type*} [Group G] {x y z : G} (hy : x * y = y * x)
    (hz : x * z = z * x) : x * (y * z) = y * z * x := by
  rw [← mul_assoc, hy, mul_assoc, hz, ← mul_assoc]

private theorem mul_div_cancel_aux' {a : K} (ha : a ≠ 0) (c : K) : a * (c / a) = c := by
  rw [mul_div_assoc', mul_div_cancel_left₀ c ha]

theorem transvGL_mul_same (i j : Fin 6) (hij : i ≠ j) (c d : K) :
    transvGL K i j hij c * transvGL K i j hij d = transvGL K i j hij (c + d) := by
  apply Units.ext
  simp only [Units.val_mul, transvGL_val]
  exact Matrix.transvection_mul_transvection_same i j hij c d

theorem transvGL_commute (i j k l : Fin 6) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : K) :
    transvGL K i j hij a * transvGL K k l hkl b = transvGL K k l hkl b * transvGL K i j hij a := by
  apply Units.ext
  simp only [Units.val_mul, transvGL_val]
  exact transvection_comm_aux hjk hli a b

theorem steinberg (i j k : Fin 6) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : K) :
    ⁅transvGL K i j hij a, transvGL K j k hjk b⁆ = transvGL K i k hik (a * b) := by
  apply comm_eq_of_mul_eq
  apply Units.ext
  simp only [Units.val_mul, transvGL_val]
  exact steinberg_aux hjk hik a b

theorem diagGL_comm_transvGL (d : Fin 6 → K) (hd : ∀ i, d i ≠ 0) (i j : Fin 6) (hij : i ≠ j)
    (c : K) :
    ⁅diagGL d hd, transvGL K i j hij c⁆ = transvGL K i j hij ((d i / d j - 1) * c) := by
  apply comm_eq_of_mul_eq
  apply Units.ext
  simp only [Units.val_mul, diagGL_val, transvGL_val]
  exact diag_transvection_aux d hd i j hij c

theorem diagGL_commute_transvGL (d : Fin 6 → K) (hd : ∀ i, d i ≠ 0) (k l : Fin 6) (hkl : k ≠ l)
    (c : K) (h : d k = d l) :
    diagGL d hd * transvGL K k l hkl c = transvGL K k l hkl c * diagGL d hd := by
  have e : d k * c = c * d l := by rw [h, mul_comm]
  apply Units.ext
  simp only [Units.val_mul, diagGL_val, transvGL_val, Matrix.transvection, mul_add, add_mul,
    one_mul, mul_one, diagonal_mul_single_aux, single_mul_diagonal_aux, e]

@[expose] def lev2 : Fin 6 → ℕ := ![0, 2, 0, 2, 1, 1]

@[expose] def Uset1 (K : Type*) [Field K] : Set (GL (Fin 6) K) :=
  {u | ∃ (i j : Fin 6) (hij : i ≠ j) (c : K),
    ((i = 0 ∧ 1 ≤ j.val) ∨ (j = 1 ∧ 2 ≤ i.val)) ∧ u = transvGL K i j hij c}

@[expose] def Pset1 (K : Type*) [Field K] : Set (GL (Fin 6) K) :=
  {u | ∃ (i j : Fin 6) (hij : i ≠ j) (c : K), 2 ≤ i.val ∧ i.val < j.val ∧ u = transvGL K i j hij c}

@[expose] def Uset2 (K : Type*) [Field K] : Set (GL (Fin 6) K) :=
  {u | ∃ (i j : Fin 6) (hij : i ≠ j) (c : K), lev2 i < lev2 j ∧ u = transvGL K i j hij c}

private theorem idx_Uset1 : ∀ i j : Fin 6, ((i = 0 ∧ 1 ≤ j.val) ∨ (j = 1 ∧ 2 ≤ i.val)) →
    j ≠ 0 ∧ (1 : Fin 6) ≠ i := by
  decide

private theorem idx_Pset1 : ∀ i j : Fin 6, 2 ≤ i.val → i.val < j.val →
    j ≠ 0 ∧ (1 : Fin 6) ≠ i ∧ i ≠ 0 ∧ i ≠ 1 ∧ j ≠ 0 ∧ j ≠ 1 := by
  decide

private theorem idx_Uset2 : ∀ i j : Fin 6, lev2 i < lev2 j →
    j ≠ 0 ∧ (1 : Fin 6) ≠ i ∧ j ≠ 2 ∧ (3 : Fin 6) ≠ i := by
  decide

private theorem idx_Uset2_B : ∀ i j : Fin 6, ((i = 0 ∨ i = 2) ∧ (j = 1 ∨ j = 3)) →
    lev2 i < lev2 4 ∧ lev2 4 < lev2 j ∧ i ≠ 4 ∧ (4 : Fin 6) ≠ j := by
  decide

private theorem idx_Uset2_A : ∀ i j : Fin 6, lev2 i < lev2 j →
    ¬ ((i = 0 ∨ i = 2) ∧ (j = 1 ∨ j = 3)) →
    ((i = 0 ∨ i = 2) ∧ (j = 4 ∨ j = 5)) ∨ ((i = 4 ∨ i = 5) ∧ (j = 1 ∨ j = 3)) := by
  decide

private theorem lev2_comm_tInv2 {i j : Fin 6} (hij : i ≠ j) (c : K) (h : lev2 i < lev2 j) :
    transvGL K i j hij c * tInv2 K = tInv2 K * transvGL K i j hij c := by
  obtain ⟨h1, h2, h3, h4⟩ := idx_Uset2 i j h
  unfold tInv2 tInv1
  exact comm_mul_of_comm (transvGL_commute i j 0 1 hij (by decide) h1 h2 c 1)
    (transvGL_commute i j 2 3 hij (by decide) h3 h4 c 1)

theorem Uset1_det_commute {u : GL (Fin 6) K} (hu : u ∈ Uset1 K) :
    (u : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ u * tInv1 K = tInv1 K * u := by
  obtain ⟨i, j, hij, c, hcase, rfl⟩ := hu
  obtain ⟨h1, h2⟩ := idx_Uset1 i j hcase
  exact ⟨det_transvGL i j hij c, transvGL_commute i j 0 1 hij (by decide) h1 h2 c 1⟩

theorem Uset2_det_commute {u : GL (Fin 6) K} (hu : u ∈ Uset2 K) :
    (u : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ u * tInv2 K = tInv2 K * u := by
  obtain ⟨i, j, hij, c, hlev, rfl⟩ := hu
  exact ⟨det_transvGL i j hij c, lev2_comm_tInv2 hij c hlev⟩

private theorem exists_ne_zero_ne_one (h3 : 3 ≤ Nat.card K) : ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ l : K, l ≠ 0 → l = 1 := fun l hl => by
    by_contra h
    exact hcon ⟨l, hl, h⟩
  have hsurj : Function.Surjective (fun x : Fin 2 => if x = 0 then (0 : K) else 1) := by
    intro l
    by_cases hl : l = 0
    · exact ⟨0, by simp [hl]⟩
    · exact ⟨1, by simp [hcon' l hl]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_fin] at hle
  omega

private theorem sq_sub_one_ne_zero [CharP K 2] {l : K} (hl : l ≠ 1) : l * l - 1 ≠ 0 := by
  intro h
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h' : (l - 1) * (l - 1) = 0 := by linear_combination h - l * h2 + h2
  exact hl (sub_eq_zero.mp (mul_self_eq_zero.mp h'))

private def dP (i j : Fin 6) (l : K) : Fin 6 → K :=
  fun m => if m = i then l else if m = j then l⁻¹ else 1

private def dU (l : K) : Fin 6 → K :=
  fun m => if m = 4 then l else if m = 5 then l⁻¹ else 1

theorem Pset1_comm [CharP K 2] (h3 : 3 ≤ Nat.card K) {u : GL (Fin 6) K} (hu : u ∈ Pset1 K) :
    ∃ a b : GL (Fin 6) K, (a : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      (b : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      a * tInv1 K = tInv1 K * a ∧ b * tInv1 K = tInv1 K * b ∧ u = ⁅a, b⁆ := by
  obtain ⟨i, j, hij, c, hi2, hlt, rfl⟩ := hu
  obtain ⟨h1, h2, h3i0, h3i1, h3j0, h3j1⟩ := idx_Pset1 i j hi2 hlt
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne_one h3
  have hji : j ≠ i := hij.symm
  have hll : l * l - 1 ≠ 0 := sq_sub_one_ne_zero hl1
  have hd : ∀ m, dP i j l m ≠ 0 := by
    intro m
    unfold dP
    split_ifs <;> simp [hl0]
  have hdi : dP i j l i = l := by simp [dP]
  have hdj : dP i j l j = l⁻¹ := by simp [dP, hji]
  have h01 : dP i j l 0 = dP i j l 1 := by
    simp [dP, Ne.symm h3i0, Ne.symm h3j0, h2, Ne.symm h3j1]
  refine ⟨diagGL (dP i j l) hd, transvGL K i j hij (c / (l * l - 1)), ?_,
    det_transvGL i j hij _, ?_, ?_, ?_⟩
  · rw [det_diagGL, Fintype.prod_eq_mul i j hij ?_, hdi, hdj, mul_inv_cancel₀ hl0]
    intro m hm
    simp [dP, hm.1, hm.2]
  · unfold tInv1
    exact diagGL_commute_transvGL (dP i j l) hd 0 1 (by decide) 1 h01
  · unfold tInv1
    exact transvGL_commute i j 0 1 hij (by decide) h1 h2 _ 1
  · rw [diagGL_comm_transvGL, hdi, hdj, div_inv_eq_mul, mul_div_cancel_aux' hll c]

theorem Uset2_comm [CharP K 2] (h3 : 3 ≤ Nat.card K) {u : GL (Fin 6) K} (hu : u ∈ Uset2 K) :
    ∃ a b : GL (Fin 6) K, (a : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      (b : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      a * tInv2 K = tInv2 K * a ∧ b * tInv2 K = tInv2 K * b ∧ u = ⁅a, b⁆ := by
  obtain ⟨i, j, hij, c, hlev, rfl⟩ := hu
  by_cases hB : (i = 0 ∨ i = 2) ∧ (j = 1 ∨ j = 3)
  ·
    obtain ⟨l1, l2, hi4, h4j⟩ := idx_Uset2_B i j hB
    refine ⟨transvGL K i 4 hi4 c, transvGL K 4 j h4j 1, det_transvGL i 4 hi4 c,
      det_transvGL 4 j h4j 1, lev2_comm_tInv2 hi4 c l1, lev2_comm_tInv2 h4j 1 l2, ?_⟩
    rw [steinberg i 4 j hi4 h4j hij c 1, mul_one]
  ·
    have hA := idx_Uset2_A i j hlev hB
    obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne_one h3
    have hl1' : (1 : K) ≠ l := fun h => hl1 h.symm
    have hinv : (1 : K) ≠ l⁻¹ := fun h => hl1 (inv_eq_one.mp h.symm)
    have hinv' : l⁻¹ ≠ 1 := fun h => hl1 (inv_eq_one.mp h)
    have hd : ∀ m, dU l m ≠ 0 := by
      intro m
      unfold dU
      split_ifs <;> simp [hl0]
    have hne : dU l i ≠ dU l j := by
      rcases hA with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> rcases hi with rfl | rfl <;>
        rcases hj with rfl | rfl <;> simp [dU, hl1, hl1', hinv, hinv']
    have hdiv : dU l i / dU l j - 1 ≠ 0 := by
      intro h
      exact hne ((div_eq_one_iff_eq (hd j)).mp (sub_eq_zero.mp h))
    have hdet : (diagGL (dU l) hd : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      rw [det_diagGL, Fin.prod_univ_six]
      simp [dU, hl0]
    have hc01 : diagGL (dU l) hd * tInv1 K = tInv1 K * diagGL (dU l) hd := by
      unfold tInv1
      exact diagGL_commute_transvGL (dU l) hd 0 1 (by decide) 1 (by simp [dU])
    have hc23 : diagGL (dU l) hd * transvGL K 2 3 (by decide) 1 =
        transvGL K 2 3 (by decide) 1 * diagGL (dU l) hd :=
      diagGL_commute_transvGL (dU l) hd 2 3 (by decide) 1 (by simp [dU])
    refine ⟨diagGL (dU l) hd, transvGL K i j hij (c / (dU l i / dU l j - 1)), hdet,
      det_transvGL i j hij _, ?_, lev2_comm_tInv2 hij _ hlev, ?_⟩
    · unfold tInv2
      exact comm_mul_of_comm hc01 hc23
    · rw [diagGL_comm_transvGL, mul_div_cancel_aux' hdiv c]

end CFSG.RankThree.GF2n.Smith81.A5Cube

end

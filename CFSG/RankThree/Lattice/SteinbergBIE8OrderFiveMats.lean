module

public import CFSG.RankThree.Lattice.SteinbergBIE8OrderFiveKernel

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Polynomial Matrix

@[expose] def e8F5CWord : List (Fin Tag.E8.rank) := [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def e8F5C : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd e8F5CWord

@[expose] def e8F5U : WeylGroup Tag.E8 := e8F5C ^ 6

@[expose] def e8F5E (i : Fin Tag.E8.rank) : Fin Tag.E8.rank → ℤ := Pi.single i 1

@[expose] def e8F5B : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  Matrix.of fun i j => (![e8F5E 0, e8F5U • e8F5E 0, (e8F5U ^ 2) • e8F5E 0,
    (e8F5U ^ 3) • e8F5E 0, e8F5E 1, e8F5U • e8F5E 1, (e8F5U ^ 2) • e8F5E 1,
    (e8F5U ^ 3) • e8F5E 1] : Fin 8 → Fin Tag.E8.rank → ℤ) j i

@[expose] def e8F5Chain : Fin 4 → Fin Tag.E8.rank := ![0, 2, 3, 4]

@[expose] def e8F5J : Set (Fin Tag.E8.rank) := {0, 2, 3, 4}

theorem weylMatrix_wordProd_of {τ : Tag} {ω : List (Fin τ.rank)}
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (h : ∀ j : Fin τ.rank, ω.foldr (reflect τ) (Pi.single j 1) = fun i => M i j) :
    weylMatrix ((coxeterSystem τ).wordProd ω) = M := by
  ext i j
  rw [weylMatrix_apply, wordProd_smul]
  exact congrFun (h j) i

theorem weylMatrix_e8F5C : weylMatrix e8F5C = toMat Tag.E8.rank e8F5CList :=
  weylMatrix_wordProd_of (by decide +kernel)

theorem weylMatrix_e8F5C_pow (k : ℕ) :
    weylMatrix (e8F5C ^ k) = toMat Tag.E8.rank (lpow Tag.E8.rank e8F5CList k) := by
  rw [weylMatrix_pow, weylMatrix_e8F5C, toMat_lpow]

theorem weylMatrix_e8F5U : weylMatrix e8F5U = toMat Tag.E8.rank e8F5UList := by
  rw [e8F5U, weylMatrix_e8F5C_pow]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8F5U_pow_five : e8F5U ^ 5 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e8F5U, weylMatrix_one, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem weylMatrix_e8F5C_15 : weylMatrix (e8F5C ^ 15) = -1 := by
  rw [weylMatrix_e8F5C_pow, neg_one_eq_toMat]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem weylMatrix_e8F5C_21 : weylMatrix (e8F5C ^ 21) = -weylMatrix e8F5U := by
  rw [show e8F5C ^ 21 = e8F5C ^ 15 * e8F5U by rw [e8F5U, ← pow_add], weylMatrix_mul,
    weylMatrix_e8F5C_15, neg_one_mul]

theorem e8F5C_21_smul (x : Fin Tag.E8.rank → ℤ) : (e8F5C ^ 21) • x = -(e8F5U • x) := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, weylMatrix_e8F5C_21, Matrix.neg_mulVec]

theorem e8F5_smul_U (x : Fin Tag.E8.rank → ℤ) :
    e8F5U • x = toMat Tag.E8.rank e8F5UList *ᵥ x := by
  rw [← weylMatrix_mulVec, weylMatrix_e8F5U]

theorem e8F5_smul_U_pow (k : ℕ) (x : Fin Tag.E8.rank → ℤ) :
    (e8F5U ^ k) • x = (toMat Tag.E8.rank e8F5UList ^ k) *ᵥ x := by
  rw [← weylMatrix_mulVec, weylMatrix_pow, weylMatrix_e8F5U]

theorem e8F5B_eq : e8F5B = toMat Tag.E8.rank e8F5BList := by
  have hcols : ∀ j : Fin Tag.E8.rank,
      (fun i => e8F5B i j) = fun i => toMat Tag.E8.rank e8F5BList i j := by
    intro j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by
      fin_cases j <;> decide
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show e8F5E 0 = _
      decide +kernel
    · show e8F5U • e8F5E 0 = _
      rw [e8F5_smul_U]
      decide +kernel
    · show (e8F5U ^ 2) • e8F5E 0 = _
      rw [e8F5_smul_U_pow, ← toMat_lpow]
      decide +kernel
    · show (e8F5U ^ 3) • e8F5E 0 = _
      rw [e8F5_smul_U_pow, ← toMat_lpow]
      decide +kernel
    · show e8F5E 1 = _
      decide +kernel
    · show e8F5U • e8F5E 1 = _
      rw [e8F5_smul_U]
      decide +kernel
    · show (e8F5U ^ 2) • e8F5E 1 = _
      rw [e8F5_smul_U_pow, ← toMat_lpow]
      decide +kernel
    · show (e8F5U ^ 3) • e8F5E 1 = _
      rw [e8F5_smul_U_pow, ← toMat_lpow]
      decide +kernel
  ext i j
  exact congrFun (hcols j) i

theorem e8F5B_mul_inv :
    toMat Tag.E8.rank e8F5BList * toMat Tag.E8.rank e8F5BInv = 1 := by
  rw [← toMat_lmul, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8F5_inv_mul_B :
    toMat Tag.E8.rank e8F5BInv * toMat Tag.E8.rank e8F5BList = 1 :=
  mul_eq_one_comm.1 e8F5B_mul_inv

theorem e8F5B_det : e8F5B.det = 1 := by
  rw [e8F5B_eq, det_toMat_eq_of_colAdds _ e8F5BOps (by decide +kernel) (by decide +kernel)]
  decide +kernel

@[expose] def e8F5Conj : List (List ℤ) :=
  lmul Tag.E8.rank (lmul Tag.E8.rank e8F5BInv e8F5UList) e8F5BList

@[expose] def e8F5K : List (List ℤ) := [[0, 0, 0, -1], [1, 0, 0, -1], [0, 1, 0, -1], [0, 0, 1, -1]]

theorem e8F5Conj_blocks :
    lowerLeftZero 4 4 e8F5Conj = true ∧ ltopLeft 4 e8F5Conj = e8F5K ∧
      lbotRight 4 4 e8F5Conj = e8F5K := by
  decide +kernel

theorem e8F5_companion_charpoly :
    (toMat 4 e8F5K).charpoly = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 :=
  charpoly_eq_of_lists (cs := [1, 1, 1, 1, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [1, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 4) (by decide +kernel))

theorem e8F5_charpoly :
    (weylMatrix e8F5U).charpoly = (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2 := by
  rw [weylMatrix_e8F5U]
  have hc : (toMat Tag.E8.rank e8F5UList).charpoly = (toMat Tag.E8.rank e8F5Conj).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E8.rank e8F5BList)
      (B' := toMat Tag.E8.rank e8F5BInv) e8F5B_mul_inv, e8F5Conj, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e8F5Conj_blocks
  have hb := charpoly_eq_mul_of_blocks (k := 4) (m := 4) e8F5Conj h₁
  rw [h₂, h₃, e8F5_companion_charpoly] at hb
  rw [hc]
  refine Eq.trans (hb : (toMat Tag.E8.rank e8F5Conj).charpoly = _) ?_
  ring

section Eigen

variable {K : Type*} [CommRing K]

theorem charVal_e8F5Z_col (r a b : K) (j : Fin Tag.E8.rank) :
    charVal (e8F5Z r a b) (fun i => toMat Tag.E8.rank e8F5BList i j) = e8F5Y r a b j := by
  rw [e8F5Z, charVal_mulVec]
  have e : (toMat Tag.E8.rank e8F5BInv).mulVec (fun i => toMat Tag.E8.rank e8F5BList i j) =
      Pi.single j 1 := by
    funext i
    have := congrFun (congrFun e8F5_inv_mul_B i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [Matrix.mulVec, dotProduct, this, Pi.single_apply]
  rw [e, charVal_single]

theorem charVal_sub_col8 (z z' : Fin Tag.E8.rank → K) (x : Fin Tag.E8.rank → ℤ) :
    charVal (z - z') x = charVal z x - charVal z' x := by
  simp only [charVal, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem e8F5U_smul_col (j : Fin Tag.E8.rank) :
    e8F5U • (fun i => toMat Tag.E8.rank e8F5BList i j) =
      toMat Tag.E8.rank e8F5BList *ᵥ fun m => toMat Tag.E8.rank e8F5Conj m j := by
  rw [e8F5_smul_U]
  have h : toMat Tag.E8.rank e8F5BList * toMat Tag.E8.rank e8F5Conj =
      toMat Tag.E8.rank e8F5UList * toMat Tag.E8.rank e8F5BList := by
    rw [e8F5Conj, toMat_lmul, toMat_lmul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e8F5B_mul_inv,
      Matrix.one_mul]
  funext i
  have := congrFun (congrFun h i) j
  simp only [Matrix.mul_apply] at this
  simp only [Matrix.mulVec, dotProduct]
  rw [← this]

theorem e8F5Y_vals (r a b : K) :
    e8F5Y r a b 0 = a ∧ e8F5Y r a b 1 = r * a ∧ e8F5Y r a b 2 = r ^ 2 * a ∧
      e8F5Y r a b 3 = r ^ 3 * a ∧ e8F5Y r a b 4 = b ∧ e8F5Y r a b 5 = r * b ∧
      e8F5Y r a b 6 = r ^ 2 * b ∧ e8F5Y r a b 7 = r ^ 3 * b := by
  have e8 : Tag.E8.rank = 8 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [e8F5Y, e8]

@[expose] def e8F5Col (j : Fin Tag.E8.rank) : Fin Tag.E8.rank → ℤ :=
  fun i => toMat Tag.E8.rank e8F5BList i j

theorem e8F5U_cols :
    e8F5U • e8F5Col 0 = e8F5Col 1 ∧ e8F5U • e8F5Col 1 = e8F5Col 2 ∧
      e8F5U • e8F5Col 2 = e8F5Col 3 ∧
      e8F5U • e8F5Col 3 = -(e8F5Col 0 + e8F5Col 1 + e8F5Col 2 + e8F5Col 3) ∧
      e8F5U • e8F5Col 4 = e8F5Col 5 ∧ e8F5U • e8F5Col 5 = e8F5Col 6 ∧
      e8F5U • e8F5Col 6 = e8F5Col 7 ∧
      e8F5U • e8F5Col 7 = -(e8F5Col 4 + e8F5Col 5 + e8F5Col 6 + e8F5Col 7) := by
  simp only [e8F5_smul_U]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem e8F5_eigen_of {r : K} (hr : r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = 0) (a b : K) :
    (dualMatrix K e8F5U).mulVec (e8F5Z r a b) = r • e8F5Z r a b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_charVal_columns e8F5B_mul_inv fun j => ?_
  rw [charVal_sub_col8, charVal_dualMatrix, charVal_smul_col, sub_eq_zero]
  change charVal (e8F5Z r a b) (e8F5U • e8F5Col j) = r * charVal (e8F5Z r a b) (e8F5Col j)
  have hc : ∀ k, charVal (e8F5Z r a b) (e8F5Col k) = e8F5Y r a b k := charVal_e8F5Z_col r a b
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ := e8F5Y_vals r a b
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7⟩ := e8F5U_cols
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by
    fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u0, hc, hc, y0, y1]
  · rw [u1, hc, hc, y1, y2]
    ring
  · rw [u2, hc, hc, y2, y3]
    ring
  · rw [u3, charVal_neg, charVal_add, charVal_add, charVal_add, hc, hc, hc, hc, y0, y1, y2, y3]
    linear_combination (-a) * hr
  · rw [u4, hc, hc, y4, y5]
  · rw [u5, hc, hc, y5, y6]
    ring
  · rw [u6, hc, hc, y6, y7]
    ring
  · rw [u7, charVal_neg, charVal_add, charVal_add, charVal_add, hc, hc, hc, hc, y4, y5, y6, y7]
    linear_combination (-b) * hr

theorem e8F5Col_eq : e8F5Col 0 = e8F5E 0 ∧ e8F5Col 1 = e8F5U • e8F5E 0 ∧
    e8F5Col 2 = (e8F5U ^ 2) • e8F5E 0 ∧ e8F5Col 3 = (e8F5U ^ 3) • e8F5E 0 ∧
    e8F5Col 4 = e8F5E 1 ∧ e8F5Col 5 = e8F5U • e8F5E 1 ∧
    e8F5Col 6 = (e8F5U ^ 2) • e8F5E 1 ∧ e8F5Col 7 = (e8F5U ^ 3) • e8F5E 1 := by
  have h : ∀ j, e8F5Col j = fun i => e8F5B i j := fun j => by
    funext i
    rw [e8F5Col, e8F5B_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h] <;> rfl

theorem e8F5_eigen_eq {r : K} {z : Fin Tag.E8.rank → K}
    (hz : (dualMatrix K e8F5U).mulVec z = r • z) :
    z = e8F5Z r (charVal z (e8F5E 0)) (charVal z (e8F5E 1)) := by
  have hU : ∀ x, charVal z (e8F5U • x) = r * charVal z x := fun x => by
    rw [← charVal_dualMatrix, hz, charVal_smul_col]
  have hU2 : ∀ x, charVal z ((e8F5U ^ 2) • x) = r ^ 2 * charVal z x := fun x => by
    rw [sq, mul_smul, hU, hU, ← mul_assoc, sq]
  have hU3 : ∀ x, charVal z ((e8F5U ^ 3) • x) = r ^ 3 * charVal z x := fun x => by
    rw [pow_succ, mul_smul, hU2, hU]
    ring
  rw [← sub_eq_zero]
  refine eq_zero_of_charVal_columns e8F5B_mul_inv fun j => ?_
  rw [charVal_sub_col8, charVal_e8F5Z_col, sub_eq_zero]
  change charVal z (e8F5Col j) = _
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ :=
    e8F5Y_vals r (charVal z (e8F5E 0)) (charVal z (e8F5E 1))
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := e8F5Col_eq
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by
    fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [c0, y0]
  · rw [c1, hU, y1]
  · rw [c2, hU2, y2]
  · rw [c3, hU3, y3]
  · rw [c4, y4]
  · rw [c5, hU, y5]
  · rw [c6, hU2, y6]
  · rw [c7, hU3, y7]

theorem e8F5Z_coords (r a b : K) :
    charVal (e8F5Z r a b) (e8F5E 0) = a ∧ charVal (e8F5Z r a b) (e8F5E 1) = b := by
  obtain ⟨c0, -, -, -, c4, -⟩ := e8F5Col_eq
  obtain ⟨y0, -, -, -, y4, -⟩ := e8F5Y_vals r a b
  refine ⟨?_, ?_⟩
  · rw [← c0]
    exact (charVal_e8F5Z_col r a b 0).trans y0
  · rw [← c4]
    exact (charVal_e8F5Z_col r a b 4).trans y4

theorem e8F5Z_zero (r : K) : e8F5Z r 0 0 = 0 := by
  rw [e8F5Z]
  have : e8F5Y r (0 : K) 0 = 0 := by
    funext k
    simp only [e8F5Y, mul_zero, ite_self, Pi.zero_apply]
  rw [this, Matrix.mulVec_zero]

end Eigen

instance e8F5_fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

@[expose] def e8F5ConjWord (ω : List (Fin Tag.E8.rank)) : List (Fin Tag.E8.rank) :=
  ω ++ (e8F5CWord ++ e8F5CWord ++ e8F5CWord ++ e8F5CWord ++ e8F5CWord ++ e8F5CWord) ++ ω.reverse

theorem e8F5U_eq_wordProd : e8F5U = (coxeterSystem Tag.E8).wordProd
    (e8F5CWord ++ e8F5CWord ++ e8F5CWord ++ e8F5CWord ++ e8F5CWord ++ e8F5CWord) := by
  simp only [e8F5U, e8F5C, pow_succ, pow_zero, one_mul, CoxeterSystem.wordProd_append]

theorem e8F5_conj_smul (ω : List (Fin Tag.E8.rank)) (x : Fin Tag.E8.rank → ℤ) :
    ((coxeterSystem Tag.E8).wordProd ω * e8F5U * ((coxeterSystem Tag.E8).wordProd ω)⁻¹) • x =
      (e8F5ConjWord ω).foldr (reflect Tag.E8) x := by
  rw [e8F5U_eq_wordProd, ← CoxeterSystem.wordProd_reverse, ← CoxeterSystem.wordProd_append,
    ← CoxeterSystem.wordProd_append, wordProd_smul]
  rfl

theorem e8_smul_neg (g : WeylGroup Tag.E8) (x : Fin Tag.E8.rank → ℤ) : g • (-x) = -(g • x) := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, Matrix.mulVec_neg]

@[expose] def e8F5SuppOK (ω : List (Fin Tag.E8.rank)) (i : ℕ) : Bool :=
  (e8F5ClassRoots i).all fun l => (List.finRange 8).all fun k =>
    decide (k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 4) ||
      decide ((ω.foldr (reflect Tag.E8) (toVec Tag.E8.rank l)) k = 0)

theorem mem_e8F5J (k : Fin Tag.E8.rank) : k ∈ e8F5J ↔ k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
  simp [e8F5J]

theorem ncard_parabolicRoots_e8F5J : (parabolicRoots Tag.E8 e8F5J).ncard = 20 := by
  have e : parabolicRoots Tag.E8 e8F5J =
      {v | IsRoot Tag.E8 v ∧
        ∀ k : Fin Tag.E8.rank, ¬(k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 4) → v k = 0} := by
    ext v
    simp only [parabolicRoots, Set.mem_ofPred_eq, mem_e8F5J]
  rw [e, ncard_isRoot_and]
  decide +kernel

theorem e8F5_transport_of_checks {i : ℕ} (hi : i < 12) (ω : List (Fin Tag.E8.rank))
    (π : Equiv.Perm (Fin 5)) (hsupp : e8F5SuppOK ω i = true)
    (hπ : ∀ kl : Fin 5 × Fin 5, (e8F5ConjWord ω).foldr (reflect Tag.E8)
      (chainRoot e8F5Chain kl.1 kl.2) = chainRoot e8F5Chain (π kl.1) (π kl.2))
    (h5 : π ^ 5 = 1 ∧ π ≠ 1) :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet i = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain := by
  set a := (coxeterSystem Tag.E8).wordProd ω with ha
  have hsub : (a • ·) '' e8F5ClassSet i ⊆ parabolicRoots Tag.E8 e8F5J := by
    rintro _ ⟨α, hα, rfl⟩
    refine ⟨IsRoot.smul (isRoot_of_mem_classSet hi hα) a, fun k hk => ?_⟩
    have h1 := List.all_eq_true.1 hsupp _ hα
    have h2 := List.all_eq_true.1 h1 k (List.mem_finRange k)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
    rcases h2 with h2 | h2
    · exact absurd ((mem_e8F5J k).2 h2) hk
    · show ((coxeterSystem Tag.E8).wordProd ω • α) k = 0
      rw [wordProd_smul]
      rwa [toVec_ofFn] at h2
  have hcard : (a • ·) '' e8F5ClassSet i = parabolicRoots Tag.E8 e8F5J := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ ((finite_setOf_isRoot Tag.E8).subset
      fun _ h => h.1)
    rw [ncard_parabolicRoots_e8F5J, Set.ncard_image_of_injective _ (MulAction.injective a),
      ncard_classSet hi]
  have hT : ∀ k l, (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l =
      chainRoot e8F5Chain (π k) (π l) := fun k l => by
    rw [ha, e8F5_conj_smul]
    exact hπ (k, l)
  refine ⟨a, hcard, ⟨π, orderOf_eq_prime h5.1 h5.2, hT⟩, π, fun k l => ?_⟩
  show (a * e8F5C ^ 21 * a⁻¹) • chainRoot e8F5Chain k l = _
  rw [mul_smul, mul_smul, e8F5C_21_smul, e8_smul_neg, ← mul_smul, ← mul_smul, hT,
    chainRoot_swap, neg_neg]

end CFSG.RankThree.Lattice

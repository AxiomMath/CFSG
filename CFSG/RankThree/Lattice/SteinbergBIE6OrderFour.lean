module

public import CFSG.RankThree.Lattice.SteinbergBIE6OrderFourStab
public import CFSG.RankThree.Lattice.SteinbergBIDet

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Polynomial Matrix

instance e6F4_fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

@[expose] def e6F4CWord : List (Fin 6) := [0, 1, 2, 3, 4]

@[expose] def e6F4C : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word e6F4CWord)

@[expose] def e6F4U : WeylGroup Tag.E6 := e6F4C ^ 2

@[expose] def e6F4V : Fin Tag.E6.rank → ℤ := Pi.single 5 1

@[expose] def e6F4B : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  Matrix.of fun i j => (![e6F4V, e6F4U • e6F4V, (e6F4U ^ 2) • e6F4V, e6F4C • e6F4V,
    e6F4U • e6F4C • e6F4V, (e6F4U ^ 2) • e6F4C • e6F4V] : Fin 6 → Fin Tag.E6.rank → ℤ) j i

@[expose] def e6F4BList : List (List ℤ) :=
  [[0, 1, 1, 1, 1, 0], [0, 1, 1, 1, 2, 1], [0, 2, 2, 1, 2, 1], [0, 2, 3, 1, 3, 2],
   [0, 1, 2, 1, 2, 2], [1, 1, 1, 1, 1, 1]]

@[expose] def e6F4BInv : List (List ℤ) :=
  [[0, 0, -1, 1, -1, 1], [-1, 0, 2, -1, 0, 0], [1, -1, -1, 1, 0, 0], [1, 0, 0, -1, 1, 0],
   [0, 1, -1, 1, -1, 0], [-1, 0, 1, -1, 1, 0]]

@[expose] def e6F4UList : List (List ℤ) :=
  [[0, 0, 1, -1, 0, 1], [1, 1, 0, -1, 0, 1], [0, 1, 1, -1, -1, 2], [1, 1, 1, -1, -1, 2],
   [0, 1, 1, -1, 0, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def e6F4CList : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 1], [0, 0, 1, 0, -1, 1], [1, 1, 0, 0, -1, 1], [0, 1, 1, 0, -1, 1],
   [0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 1]]

theorem e6F4U_eq : e6F4U = (coxeterSystem Tag.E6).wordProd (e6Word (e6F4CWord ++ e6F4CWord)) := by
  rw [e6F4U, e6F4C, sq, ← CoxeterSystem.wordProd_append]
  rfl

theorem weylMatrix_e6F4C : weylMatrix e6F4C = toMat Tag.E6.rank e6F4CList :=
  weylMatrix_wordProd_e6 (by decide +kernel)

theorem weylMatrix_e6F4U : weylMatrix e6F4U = toMat Tag.E6.rank e6F4UList := by
  rw [e6F4U_eq]
  exact weylMatrix_wordProd_e6 (by decide +kernel)

theorem e6F4_smul_U (x : Fin Tag.E6.rank → ℤ) :
    e6F4U • x = toMat Tag.E6.rank e6F4UList *ᵥ x := by
  rw [← weylMatrix_mulVec, weylMatrix_e6F4U]

theorem e6F4_smul_U2 (x : Fin Tag.E6.rank → ℤ) :
    (e6F4U ^ 2) • x = toMat Tag.E6.rank e6F4UList *ᵥ (toMat Tag.E6.rank e6F4UList *ᵥ x) := by
  rw [sq, mul_smul, e6F4_smul_U, e6F4_smul_U]

theorem e6F4_smul_C (x : Fin Tag.E6.rank → ℤ) :
    e6F4C • x = toMat Tag.E6.rank e6F4CList *ᵥ x := by
  rw [← weylMatrix_mulVec, weylMatrix_e6F4C]

theorem e6F4B_eq : e6F4B = toMat Tag.E6.rank e6F4BList := by
  have hcols : ∀ j : Fin Tag.E6.rank,
      (fun i => e6F4B i j) = fun i => toMat Tag.E6.rank e6F4BList i j := by
    intro j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
      fin_cases j <;> decide
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · show e6F4V = _
      decide +kernel
    · show e6F4U • e6F4V = _
      rw [e6F4_smul_U]
      decide +kernel
    · show (e6F4U ^ 2) • e6F4V = _
      rw [e6F4_smul_U2]
      decide +kernel
    · show e6F4C • e6F4V = _
      rw [e6F4_smul_C]
      decide +kernel
    · show e6F4U • e6F4C • e6F4V = _
      rw [e6F4_smul_C, e6F4_smul_U]
      decide +kernel
    · show (e6F4U ^ 2) • e6F4C • e6F4V = _
      rw [e6F4_smul_C, e6F4_smul_U2]
      decide +kernel
  ext i j
  exact congrFun (hcols j) i

theorem e6F4B_mul_inv :
    toMat Tag.E6.rank e6F4BList * toMat Tag.E6.rank e6F4BInv = 1 := by
  rw [← toMat_lmul, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6F4_inv_mul_B :
    toMat Tag.E6.rank e6F4BInv * toMat Tag.E6.rank e6F4BList = 1 :=
  mul_eq_one_comm.1 e6F4B_mul_inv

theorem e6F4B_det : e6F4B.det = -1 := by
  rw [e6F4B_eq, det_toMat_eq]
  decide +kernel

theorem e6F4U_pow_four : e6F4U ^ 4 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e6F4U, weylMatrix_one, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

@[expose] def e6F4Conj : List (List ℤ) :=
  lmul Tag.E6.rank (lmul Tag.E6.rank e6F4BInv e6F4UList) e6F4BList

theorem e6F4Conj_blocks :
    lowerLeftZero 3 3 e6F4Conj = true ∧
      ltopLeft 3 e6F4Conj = [[0, 0, 1], [1, 0, -1], [0, 1, 1]] ∧
      lbotRight 3 3 e6F4Conj = [[0, 0, 1], [1, 0, -1], [0, 1, 1]] := by
  decide +kernel

theorem e6F4_companion_charpoly :
    (toMat 3 [[0, 0, 1], [1, 0, -1], [0, 1, 1]]).charpoly = X ^ 3 - X ^ 2 + X - 1 :=
  charpoly_eq_of_lists (cs := [-1, 1, -1, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [1, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 3) (by decide +kernel))

theorem e6F4_charpoly :
    (weylMatrix e6F4U).charpoly = (X - 1) ^ 2 * (X ^ 2 + 1) ^ 2 := by
  rw [weylMatrix_e6F4U]
  have hc : (toMat Tag.E6.rank e6F4UList).charpoly = (toMat Tag.E6.rank e6F4Conj).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E6.rank e6F4BList)
      (B' := toMat Tag.E6.rank e6F4BInv) e6F4B_mul_inv, e6F4Conj, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e6F4Conj_blocks
  have hb := charpoly_eq_mul_of_blocks (k := 3) (m := 3) e6F4Conj h₁
  rw [h₂, h₃, e6F4_companion_charpoly] at hb
  rw [hc]
  refine Eq.trans (hb : (toMat Tag.E6.rank e6F4Conj).charpoly = _) ?_
  ring

theorem e6F4_kills (x : Fin Tag.E6.rank → ℤ) (hx : x = e6F4V ∨ x = e6F4C • e6F4V) :
    (((weylMatrix e6F4U) ^ 2 + 1) * (weylMatrix e6F4U - 1)) *ᵥ x = 0 := by
  have e : ((weylMatrix e6F4U) ^ 2 + 1) * (weylMatrix e6F4U - 1) =
      toMat Tag.E6.rank (lmul Tag.E6.rank
        (ladd Tag.E6.rank (lmul Tag.E6.rank e6F4UList e6F4UList) (lid Tag.E6.rank))
        (ladd Tag.E6.rank e6F4UList (lsmul Tag.E6.rank (-1) (lid Tag.E6.rank)))) := by
    rw [toMat_lmul, toMat_ladd, toMat_ladd, toMat_lmul, toMat_lsmul, toMat_lid, weylMatrix_e6F4U,
      sq, neg_one_smul, ← sub_eq_add_neg]
  rw [e]
  rcases hx with rfl | rfl
  · decide +kernel
  · rw [e6F4_smul_C]
    decide +kernel

@[expose] def e6F4Y (r a b : ZMod 5) : Fin Tag.E6.rank → ZMod 5 :=
  fun k => if (k : ℕ) < 3 then r ^ (k : ℕ) * a else r ^ ((k : ℕ) - 3) * b

@[expose] def e6F4Z (r a b : ZMod 5) : Fin Tag.E6.rank → ZMod 5 :=
  (((toMat Tag.E6.rank e6F4BInv).map (Int.cast : ℤ → ZMod 5)).transpose).mulVec (e6F4Y r a b)

theorem charVal_sub_col {R : Type*} [CommRing R] (z z' : Fin Tag.E6.rank → R)
    (x : Fin Tag.E6.rank → ℤ) : charVal (z - z') x = charVal z x - charVal z' x := by
  simp only [charVal, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem charVal_e6F4Z (r a b : ZMod 5) (j : Fin Tag.E6.rank) :
    charVal (e6F4Z r a b) (fun i => toMat Tag.E6.rank e6F4BList i j) = e6F4Y r a b j := by
  rw [e6F4Z, charVal_mulVec]
  have e : (toMat Tag.E6.rank e6F4BInv).mulVec (fun i => toMat Tag.E6.rank e6F4BList i j) =
      Pi.single j 1 := by
    funext i
    have := congrFun (congrFun e6F4_inv_mul_B i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [Matrix.mulVec, dotProduct, this, Pi.single_apply]
  rw [e, charVal_single]

theorem e6F4Y_smul (r s a b : ZMod 5) : e6F4Y r (s * a) (s * b) = s • e6F4Y r a b := by
  funext k
  simp only [e6F4Y, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem e6F4Z_smul (r s a b : ZMod 5) : e6F4Z r (s * a) (s * b) = s • e6F4Z r a b := by
  rw [e6F4Z, e6F4Z, e6F4Y_smul, Matrix.mulVec_smul]

theorem e6F4_eigen_eq {r : ZMod 5} {z : Fin Tag.E6.rank → ZMod 5}
    (hz : (dualMatrix (ZMod 5) e6F4U).mulVec z = r • z) :
    z = e6F4Z r (charVal z e6F4V) (charVal z (e6F4C • e6F4V)) := by
  have hU : ∀ x, charVal z (e6F4U • x) = r * charVal z x := fun x => by
    rw [← charVal_dualMatrix, hz, charVal_smul_col]
  rw [← sub_eq_zero]
  refine eq_zero_of_charVal_columns e6F4B_mul_inv fun j => ?_
  rw [charVal_sub_col, charVal_e6F4Z, sub_eq_zero]
  have hcol : (fun i => toMat Tag.E6.rank e6F4BList i j) = fun i => e6F4B i j := by
    rw [e6F4B_eq]
  rw [hcol]
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
    fin_cases j <;> decide
  have hU2 : ∀ x, charVal z ((e6F4U ^ 2) • x) = r ^ 2 * charVal z x := fun x => by
    rw [sq, mul_smul, hU, hU, ← mul_assoc, sq]
  have hr6 : Tag.E6.rank = 6 := rfl
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · show charVal z e6F4V = _
    simp [e6F4Y, hr6]
  · show charVal z (e6F4U • e6F4V) = _
    rw [hU]
    simp [e6F4Y, hr6]
  · show charVal z ((e6F4U ^ 2) • e6F4V) = _
    rw [hU2]
    simp [e6F4Y, hr6]
  · show charVal z (e6F4C • e6F4V) = _
    simp [e6F4Y, hr6]
  · show charVal z (e6F4U • e6F4C • e6F4V) = _
    rw [hU]
    simp [e6F4Y, hr6]
  · show charVal z ((e6F4U ^ 2) • e6F4C • e6F4V) = _
    rw [hU2]
    simp [e6F4Y, hr6]

theorem e6F4_eigen_rep {r : ZMod 5} {z : Fin Tag.E6.rank → ZMod 5} (hz0 : z ≠ 0)
    (hz : (dualMatrix (ZMod 5) e6F4U).mulVec z = r • z) :
    ∃ s : ZMod 5, s ≠ 0 ∧ ((∃ j : ZMod 5, z = s • e6F4Z r 1 j) ∨ z = s • e6F4Z r 0 1) := by
  have h := e6F4_eigen_eq hz
  set a := charVal z e6F4V
  set b := charVal z (e6F4C • e6F4V)
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      apply hz0
      rw [h, ha, hb, show (0 : ZMod 5) = 0 * 0 by ring, e6F4Z_smul, zero_smul]
    refine ⟨b, hb, Or.inr ?_⟩
    rw [h, ha, ← e6F4Z_smul, mul_zero, mul_one]
  · refine ⟨a, ha, Or.inl ⟨b * a⁻¹, ?_⟩⟩
    rw [h, ← e6F4Z_smul, mul_one, mul_comm b, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

@[expose] def E6F4Claims (z : Fin Tag.E6.rank → ZMod 5) : Prop :=
  (∃ a : WeylGroup Tag.E6, (a • ·) '' rootKernel z = parabolicRoots Tag.E6 support134 ∧
    (∀ i j, j ∈ support134 → i ∉ support134 → weylMatrix (a * e6F4U * a⁻¹) i j = 0) ∧
    ((weylMatrix (a * e6F4U * a⁻¹)).submatrix chain134 chain134).charpoly =
      (X - 1) * (X ^ 2 + 1) ∧
    IsNegativeTransition (fun x => (a * e6F4U * a⁻¹) • x) chain134 chain134) ∧
  (∀ g : WeylGroup Tag.E6, (dualMatrix (ZMod 5) g⁻¹).mulVec z = z ↔
    g ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) ∧
  Nat.card (Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) = 24

theorem E6F4Claims_smul {z : Fin Tag.E6.rank → ZMod 5} {s : ZMod 5} (hs : s ≠ 0)
    (h : E6F4Claims z) : E6F4Claims (s • z) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [rootKernel_smul hs]; exact h1, fun g => ?_, by rw [rootKernel_smul hs]; exact h3⟩
  rw [rootKernel_smul hs, ← h2 g, Matrix.mulVec_smul]
  exact (smul_right_injective _ hs).eq_iff

@[expose] def e6F4ConjWord (ω : List (Fin 6)) : List (Fin 6) :=
  ω ++ (e6F4CWord ++ e6F4CWord) ++ ω.reverse

theorem e6F4_conj_smul (ω : List (Fin 6)) (x : Fin Tag.E6.rank → ℤ) :
    ((coxeterSystem Tag.E6).wordProd (e6Word ω) * e6F4U *
      ((coxeterSystem Tag.E6).wordProd (e6Word ω))⁻¹) • x =
      (e6Word (e6F4ConjWord ω)).foldr (reflect Tag.E6) x := by
  rw [e6F4U_eq, wordProd_conj_e6, wordProd_smul]
  rfl

theorem e6F4_rep_of_checks {z : Fin Tag.E6.rank → ZMod 5} (ω : List (Fin 6))
    (N : List (List ℤ)) (π : Equiv.Perm (Fin 4)) (x : List ℤ)
    (hχ : ∀ i : Fin Tag.E6.rank,
      charVal e6F4ZJ ((e6Word ω).foldr (reflect Tag.E6) (Pi.single i 1)) = z i)
    (hInv : ∀ j : Fin 3, ∀ i : Fin Tag.E6.rank, ¬(i = 0 ∨ i = 2 ∨ i = 3) →
      (e6Word (e6F4ConjWord ω)).foldr (reflect Tag.E6) (Pi.single (chain134 j) 1) i = 0)
    (hN : (Matrix.of fun a b : Fin 3 => (e6Word (e6F4ConjWord ω)).foldr (reflect Tag.E6)
      (Pi.single (chain134 b) 1) (chain134 a)) = toMat 3 N)
    (hpoly : lpolyEval 3 N [-1, 1, -1, 1] = lzero 3)
    (hcyc : lorbitDet 3 N x = 1 ∨ lorbitDet 3 N x = -1)
    (hπ : ∀ ij : Fin 4 × Fin 4, (e6Word (e6F4ConjWord ω)).foldr (reflect Tag.E6)
      (chainRoot chain134 ij.1 ij.2) = chainRoot chain134 (π ij.2) (π ij.1)) :
    E6F4Claims z := by
  set a := (coxeterSystem Tag.E6).wordProd (e6Word ω) with ha
  have hrel : ∀ y, charVal e6F4ZJ (a • y) = charVal z y := fun y => by
    rw [charVal_smul_eq_sum, charVal]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha, wordProd_smul, hχ j]
  have himg : (a • ·) '' rootKernel z = parabolicRoots Tag.E6 support134 := by
    rw [image_rootKernel_of_charVal hrel, rootKernel_e6F4ZJ]
  obtain ⟨hstab, hcard⟩ := dualWeylStabilizer_e6F4ZJ
  have hmem : ∀ g, g ∈ dualWeylStabilizer z ↔
      g ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} := fun g => by
    rw [mem_dualWeylStabilizer_conj hrel, hstab, ← mem_closure_rootKernel_conj hrel]
  refine ⟨⟨a, himg, ?_, ?_, ?_⟩, fun g => ?_, ?_⟩
  · intro i j hj hi
    rw [weylMatrix_apply, e6F4_conj_smul]
    rw [mem_support134] at hj
    rcases hj with rfl | rfl | rfl
    · exact hInv 0 i ((mem_support134 i).not.1 hi)
    · exact hInv 1 i ((mem_support134 i).not.1 hi)
    · exact hInv 2 i ((mem_support134 i).not.1 hi)
  · have e : (weylMatrix (a * e6F4U * a⁻¹)).submatrix chain134 chain134 = toMat 3 N := by
      rw [← hN]
      ext p q
      rw [Matrix.submatrix_apply, weylMatrix_apply, e6F4_conj_smul, Matrix.of_apply]
    rw [e]
    refine charpoly_eq_of_lists (cs := [-1, 1, -1, 1]) (by monicity!) (by compute_degree!)
      (by simp [polyOfList]; ring) hpoly x ?_
    rw [det_orbitMat_toVec]
    rcases hcyc with h | h <;> rw [h]
    · exact isUnit_one
    · exact isUnit_one.neg
  · refine ⟨π, fun i j => ?_⟩
    show (a * e6F4U * a⁻¹) • chainRoot chain134 i j = _
    rw [e6F4_conj_smul]
    exact hπ (i, j)
  · rw [← mem_dualWeylStabilizer_iff_dualMatrix, hmem]
  · rw [← hcard]
    have e : dualWeylStabilizer z =
        Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} := by
      ext g
      exact hmem g
    rw [← e]
    exact Nat.card_congr
      { toFun := fun g => ⟨a * g * a⁻¹, (mem_dualWeylStabilizer_conj hrel g).1 g.2⟩
        invFun := fun g => ⟨a⁻¹ * g * a, (mem_dualWeylStabilizer_conj hrel _).2 (by
          rw [show a * (a⁻¹ * (g : WeylGroup Tag.E6) * a) * a⁻¹ = g by group]
          exact g.2)⟩
        left_inv := fun g => Subtype.ext (by simp only; group)
        right_inv := fun g => Subtype.ext (by simp only; group) }

theorem e6F4_rep_2_1_0 : E6F4Claims (e6F4Z 2 1 0) :=
  e6F4_rep_of_checks [1, 3, 4, 3, 2, 5, 4, 3, 1]
    [[0, 1, -1], [0, 1, 0], [1, 0, 0]]
    (Equiv.ofBijective (fun i => (![3, 2, 0, 1] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, -1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_2_1_1 : E6F4Claims (e6F4Z 2 1 1) :=
  e6F4_rep_of_checks [4, 3, 1, 2, 0, 3, 2, 5, 4, 3, 1, 2, 0, 3, 4, 5]
    [[0, 1, -1], [-1, 1, -1], [-1, 1, 0]]
    (Equiv.ofBijective (fun i => (![1, 3, 0, 2] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, 0] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_2_1_2 : E6F4Claims (e6F4Z 2 1 2) :=
  e6F4_rep_of_checks [4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5]
    [[1, -1, 0], [1, 0, -1], [1, 0, 0]]
    (Equiv.ofBijective (fun i => (![3, 0, 1, 2] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, -1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_2_1_3 : E6F4Claims (e6F4Z 2 1 3) :=
  e6F4_rep_of_checks [1, 3, 4, 3, 1, 2, 0, 5, 4]
    [[0, 1, -1], [0, 1, 0], [1, 0, 0]]
    (Equiv.ofBijective (fun i => (![3, 2, 0, 1] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, -1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_2_1_4 : E6F4Claims (e6F4Z 2 1 4) :=
  e6F4_rep_of_checks [1, 3, 2, 0, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3]
    [[0, 0, 1], [0, 1, 0], [-1, 1, 0]]
    (Equiv.ofBijective (fun i => (![2, 3, 1, 0] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, -1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_2_0_1 : E6F4Claims (e6F4Z 2 0 1) :=
  e6F4_rep_of_checks [1, 3, 2, 4, 3, 1, 2, 5, 4, 3, 2, 0]
    [[0, 1, -1], [0, 1, 0], [1, 0, 0]]
    (Equiv.ofBijective (fun i => (![3, 2, 0, 1] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, -1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_3_1_0 : E6F4Claims (e6F4Z 3 1 0) :=
  e6F4_rep_of_checks [1, 3, 4, 3, 2, 5, 4, 3, 1, 2]
    [[0, 1, -1], [0, 1, 0], [1, 0, 0]]
    (Equiv.ofBijective (fun i => (![3, 2, 0, 1] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, -1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_3_1_1 : E6F4Claims (e6F4Z 3 1 1) :=
  e6F4_rep_of_checks [4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5]
    [[0, 1, -1], [-1, 1, -1], [-1, 1, 0]]
    (Equiv.ofBijective (fun i => (![1, 3, 0, 2] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, 0] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_3_1_2 : E6F4Claims (e6F4Z 3 1 2) :=
  e6F4_rep_of_checks [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3]
    [[0, 1, -1], [0, 1, 0], [1, 0, 0]]
    (Equiv.ofBijective (fun i => (![3, 2, 0, 1] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, -1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_3_1_3 : E6F4Claims (e6F4Z 3 1 3) :=
  e6F4_rep_of_checks [4, 3, 2, 0, 5, 4, 3, 1, 2, 0, 3, 2, 4, 5]
    [[1, -1, 0], [1, 0, -1], [1, 0, 0]]
    (Equiv.ofBijective (fun i => (![3, 0, 1, 2] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, -1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_3_1_4 : E6F4Claims (e6F4Z 3 1 4) :=
  e6F4_rep_of_checks [1, 3, 4, 3, 5, 4, 3, 1, 2, 0]
    [[0, 1, -1], [0, 1, 0], [1, 0, 0]]
    (Equiv.ofBijective (fun i => (![3, 2, 0, 1] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, -1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem e6F4_rep_3_0_1 : E6F4Claims (e6F4Z 3 0 1) :=
  e6F4_rep_of_checks [1, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3]
    [[0, 1, -1], [0, 1, 0], [1, 0, 0]]
    (Equiv.ofBijective (fun i => (![3, 2, 0, 1] : Fin 4 → Fin 4) i) (by decide))
    [-1, -1, -1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem E6_order_four_lattice_and_exact_order_five_A3_root_kernels :
    e6F4B.det = -1 ∧ e6F4U ^ 4 = 1 ∧
    (weylMatrix e6F4U).charpoly = (X - 1) ^ 2 * (X ^ 2 + 1) ^ 2 ∧
    (((weylMatrix e6F4U) ^ 2 + 1) * (weylMatrix e6F4U - 1)) *ᵥ e6F4V = 0 ∧
    (((weylMatrix e6F4U) ^ 2 + 1) * (weylMatrix e6F4U - 1)) *ᵥ (e6F4C • e6F4V) = 0 ∧
    ∀ r : ZMod 5, (r = 2 ∨ r = 3) → ∀ z : Fin Tag.E6.rank → ZMod 5, z ≠ 0 →
      (dualMatrix (ZMod 5) e6F4U).mulVec z = r • z →
      (∃ a : WeylGroup Tag.E6, (a • ·) '' rootKernel z = parabolicRoots Tag.E6 support134 ∧
        (∀ i j, j ∈ support134 → i ∉ support134 → weylMatrix (a * e6F4U * a⁻¹) i j = 0) ∧
        ((weylMatrix (a * e6F4U * a⁻¹)).submatrix chain134 chain134).charpoly =
          (X - 1) * (X ^ 2 + 1) ∧
        IsNegativeTransition (fun x => (a * e6F4U * a⁻¹) • x) chain134 chain134) ∧
      (∀ g : WeylGroup Tag.E6, (dualMatrix (ZMod 5) g⁻¹).mulVec z = z ↔
        g ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) ∧
      Nat.card (Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) = 24 := by
  refine ⟨e6F4B_det, e6F4U_pow_four, e6F4_charpoly, e6F4_kills _ (Or.inl rfl),
    e6F4_kills _ (Or.inr rfl), fun r hr z hz0 hz => ?_⟩
  show E6F4Claims z
  obtain ⟨s, hs, hrep⟩ := e6F4_eigen_rep hz0 hz
  rcases hrep with ⟨j, rfl⟩ | rfl
  · refine E6F4Claims_smul hs ?_
    rcases hr with rfl | rfl <;> fin_cases j
    exacts [e6F4_rep_2_1_0, e6F4_rep_2_1_1, e6F4_rep_2_1_2, e6F4_rep_2_1_3, e6F4_rep_2_1_4,
      e6F4_rep_3_1_0, e6F4_rep_3_1_1, e6F4_rep_3_1_2, e6F4_rep_3_1_3, e6F4_rep_3_1_4]
  · refine E6F4Claims_smul hs ?_
    rcases hr with rfl | rfl
    exacts [e6F4_rep_2_0_1, e6F4_rep_3_0_1]

end CFSG.RankThree.Lattice

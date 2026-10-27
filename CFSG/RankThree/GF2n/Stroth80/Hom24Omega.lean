module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open Matrix
open scoped commutatorElement

variable {m : ℕ} {K : Type} [Field K]

theorem fromBlocks_mulVec_inl (P Q R S : Matrix (Fin m) (Fin m) K) (w : Fin m ⊕ Fin m → K)
    (i : Fin m) :
    (fromBlocks P Q R S *ᵥ w) (Sum.inl i) =
      (P *ᵥ fun j => w (Sum.inl j)) i + (Q *ᵥ fun j => w (Sum.inr j)) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem fromBlocks_mulVec_inr (P Q R S : Matrix (Fin m) (Fin m) K) (w : Fin m ⊕ Fin m → K)
    (i : Fin m) :
    (fromBlocks P Q R S *ᵥ w) (Sum.inr i) =
      (R *ᵥ fun j => w (Sum.inl j)) i + (S *ᵥ fun j => w (Sum.inr j)) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem fromBlocks_diag_mul_eq_one {A B : Matrix (Fin m) (Fin m) K} (hAB : A * B = 1)
    (hBA : B * A = 1) :
    fromBlocks A 0 0 Bᵀ * fromBlocks B 0 0 Aᵀ = 1 ∧
      fromBlocks B 0 0 Aᵀ * fromBlocks A 0 0 Bᵀ = 1 := by
  constructor
  · rw [fromBlocks_multiply]
    simp [← transpose_mul, hAB, hBA]
  · rw [fromBlocks_multiply]
    simp [← transpose_mul, hAB, hBA]

@[expose] def levU (A : GL (Fin m) K) : GL (Fin m ⊕ Fin m) K :=
  ⟨fromBlocks (A : Matrix (Fin m) (Fin m) K) 0 0 ((A⁻¹ : GL (Fin m) K) : Matrix _ _ K)ᵀ,
    fromBlocks ((A⁻¹ : GL (Fin m) K) : Matrix _ _ K) 0 0 (A : Matrix (Fin m) (Fin m) K)ᵀ,
    (fromBlocks_diag_mul_eq_one (Units.mul_inv A) (Units.inv_mul A)).1,
    (fromBlocks_diag_mul_eq_one (Units.mul_inv A) (Units.inv_mul A)).2⟩

@[expose] def upU (T : Matrix (Fin m) (Fin m) K) : GL (Fin m ⊕ Fin m) K :=
  ⟨fromBlocks 1 T 0 1, fromBlocks 1 (-T) 0 1, by
    rw [fromBlocks_multiply]
    simp, by
    rw [fromBlocks_multiply]
    simp⟩

@[expose] def lowU (T : Matrix (Fin m) (Fin m) K) : GL (Fin m ⊕ Fin m) K :=
  ⟨fromBlocks 1 0 T 1, fromBlocks 1 0 (-T) 1, by
    rw [fromBlocks_multiply]
    simp, by
    rw [fromBlocks_multiply]
    simp⟩

@[expose] def diagU (i : Fin m) (s : K) (hs : s ≠ 0) : GL (Fin m) K :=
  ⟨diagonal fun k => if k = i then s else 1, diagonal fun k => if k = i then s⁻¹ else 1, by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [hk, hs], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [hk, hs]⟩

@[expose] def transU (i j : Fin m) (hij : i ≠ j) : GL (Fin m) K :=
  ⟨1 + Matrix.single i j 1, 1 - Matrix.single i j 1, by
    have h : Matrix.single i j (1 : K) * Matrix.single i j 1 = 0 := by
      simp [Ne.symm hij]
    simp [add_mul, mul_sub, h], by
    have h : Matrix.single i j (1 : K) * Matrix.single i j 1 = 0 := by
      simp [Ne.symm hij]
    simp [sub_mul, mul_add, h]⟩

@[expose] def altT (i j : Fin m) (t : K) : Matrix (Fin m) (Fin m) K :=
  Matrix.single i j t + Matrix.single j i t

theorem statedQuadPlus_eq (v : Fin m ⊕ Fin m → K) :
    StatedQuadPlus m K v = ∑ i, v (Sum.inl i) * v (Sum.inr i) := rfl

theorem dotProduct_altT_mulVec [CharP K 2] {i j : Fin m} (hij : i ≠ j) (t : K)
    (y : Fin m → K) : (altT i j t *ᵥ y) ⬝ᵥ y = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [altT, add_mulVec, Matrix.single_mulVec, dotProduct, Function.update_apply, add_mul,
    Finset.sum_add_distrib, ite_mul, hij, Ne.symm hij]
  linear_combination (t * y i * y j) * h2

theorem statedQuadPlus_levU (A : GL (Fin m) K) (w : Fin m ⊕ Fin m → K) :
    StatedQuadPlus m K ((levU A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w) =
      StatedQuadPlus m K w := by
  rw [statedQuadPlus_eq, statedQuadPlus_eq]
  simp only [levU, Units.val_mk, fromBlocks_mulVec_inl, fromBlocks_mulVec_inr, zero_mulVec,
    Pi.zero_apply, add_zero, zero_add]
  change ((A : Matrix (Fin m) (Fin m) K) *ᵥ fun j => w (Sum.inl j)) ⬝ᵥ
      (((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ fun j => w (Sum.inr j)) =
    (fun j => w (Sum.inl j)) ⬝ᵥ (fun j => w (Sum.inr j))
  rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, Units.inv_mul, one_mulVec]

theorem statedQuadPlus_upU [CharP K 2] {i j : Fin m} (hij : i ≠ j) (t : K)
    (w : Fin m ⊕ Fin m → K) :
    StatedQuadPlus m K ((upU (altT i j t) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w) =
      StatedQuadPlus m K w := by
  have h := dotProduct_altT_mulVec (K := K) hij t (fun j => w (Sum.inr j))
  rw [statedQuadPlus_eq, statedQuadPlus_eq]
  simp only [upU, Units.val_mk, fromBlocks_mulVec_inl, fromBlocks_mulVec_inr, one_mulVec,
    zero_mulVec, Pi.zero_apply, zero_add, add_mul, Finset.sum_add_distrib]
  simp only [dotProduct] at h
  simp only [h, add_zero]

theorem statedQuadPlus_lowU [CharP K 2] {i j : Fin m} (hij : i ≠ j) (t : K)
    (w : Fin m ⊕ Fin m → K) :
    StatedQuadPlus m K ((lowU (altT i j t) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w) =
      StatedQuadPlus m K w := by
  have h := dotProduct_altT_mulVec (K := K) hij t (fun j => w (Sum.inl j))
  rw [statedQuadPlus_eq, statedQuadPlus_eq]
  simp only [lowU, Units.val_mk, fromBlocks_mulVec_inl, fromBlocks_mulVec_inr, one_mulVec,
    zero_mulVec, Pi.zero_apply, zero_add, add_zero, mul_add, Finset.sum_add_distrib]
  simp only [dotProduct] at h
  have h' : ∑ k, w (Sum.inl k) * (altT i j t *ᵥ fun j => w (Sum.inl j)) k = 0 := by
    simp only [mul_comm (w _)] at h ⊢
    exact h
  rw [h', zero_add]

theorem commutator_levU_upU_val (A : GL (Fin m) K) (T : Matrix (Fin m) (Fin m) K) :
    (⁅levU A, upU T⁆ : GL (Fin m ⊕ Fin m) K).val =
      fromBlocks 1 (-T + (A : Matrix (Fin m) (Fin m) K) * T * (A : Matrix (Fin m) (Fin m) K)ᵀ)
        0 1 := by
  rw [commutatorElement_def]
  simp only [levU, upU, Units.val_mul, Units.inv_mk, Units.val_mk]
  simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Units.mul_inv, Units.inv_mul,
    neg_zero, ← transpose_mul, transpose_one]

theorem commutator_levU_lowU_val (A : GL (Fin m) K) (T : Matrix (Fin m) (Fin m) K) :
    (⁅levU A, lowU T⁆ : GL (Fin m ⊕ Fin m) K).val =
      fromBlocks 1 0 (((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ * T *
        ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) - T) 1 := by
  rw [commutatorElement_def]
  simp only [levU, lowU, Units.val_mul, Units.inv_mk, Units.val_mk]
  simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Units.mul_inv, Units.inv_mul,
    neg_zero, ← transpose_mul, transpose_one]
  rw [sub_eq_add_neg]

theorem commutator_levU_levU_val (A B : GL (Fin m) K) :
    (⁅levU A, levU B⁆ : GL (Fin m ⊕ Fin m) K).val =
      fromBlocks ((A : Matrix (Fin m) (Fin m) K) * (B : Matrix (Fin m) (Fin m) K) *
        ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
          ((B⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) 0 0
        (((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ *
          ((B⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ *
            (A : Matrix (Fin m) (Fin m) K)ᵀ * (B : Matrix (Fin m) (Fin m) K)ᵀ) := by
  rw [commutatorElement_def]
  simp only [levU, Units.val_mul, Units.inv_mk, Units.val_mk]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem diagU_val (i : Fin m) (s : K) (hs : s ≠ 0) :
    ((diagU i s hs : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      diagonal fun k => if k = i then s else 1 := rfl

theorem diagU_inv_val (i : Fin m) (s : K) (hs : s ≠ 0) :
    (((diagU i s hs)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      diagonal fun k => if k = i then s⁻¹ else 1 := rfl

theorem transU_val (i j : Fin m) (hij : i ≠ j) :
    ((transU (K := K) i j hij : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      1 + Matrix.single i j 1 := rfl

theorem transU_inv_val (i j : Fin m) (hij : i ≠ j) :
    (((transU (K := K) i j hij)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      1 - Matrix.single i j 1 := rfl

theorem diagonal_mul_single_mul_diagonal (d d' : Fin m → K) (i j : Fin m) (x : K) :
    diagonal d * Matrix.single i j x * diagonal d' = Matrix.single i j (d i * x * d' j) := by
  ext k l
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs <;> simp_all

theorem smul_single_one (i j : Fin m) (t : K) :
    t • (Matrix.single i j (1 : K)) = Matrix.single i j t := by
  simp [Matrix.smul_single]

theorem altT_eq_smul (i j : Fin m) (t : K) : altT i j t = t • altT i j 1 := by
  simp [altT, smul_add, Matrix.smul_single]

theorem diagU_mul_altT_mul_transpose (i j : Fin m) (hij : i ≠ j) (s : K) (hs : s ≠ 0) (t : K) :
    (diagU i s hs : Matrix (Fin m) (Fin m) K) * altT i j t *
      (diagU i s hs : Matrix (Fin m) (Fin m) K)ᵀ = altT i j (s * t) := by
  rw [diagU_val, diagonal_transpose, altT, mul_add, add_mul, diagonal_mul_single_mul_diagonal,
    diagonal_mul_single_mul_diagonal]
  simp [hij, Ne.symm hij, altT, mul_comm, mul_left_comm]

theorem diagU_inv_mul_altT_mul (i j : Fin m) (hij : i ≠ j) (s : K) (hs : s ≠ 0) (t : K) :
    (((diagU i s hs)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ * altT i j t *
      ((diagU i s hs)⁻¹ : GL (Fin m) K) = altT i j (s⁻¹ * t) := by
  rw [diagU_inv_val, diagonal_transpose, altT, mul_add, add_mul, diagonal_mul_single_mul_diagonal,
    diagonal_mul_single_mul_diagonal]
  simp [hij, Ne.symm hij, altT, mul_comm, mul_left_comm]

theorem diagU_mul_transU_mul_inv (i j : Fin m) (hij : i ≠ j) (s : K) (hs : s ≠ 0) :
    (diagU i s hs : Matrix (Fin m) (Fin m) K) *
      (transU (K := K) i j hij : Matrix (Fin m) (Fin m) K) *
      (((diagU i s hs)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
        (((transU (K := K) i j hij)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      1 + (s - 1) • Matrix.single i j 1 := by
  have hDD : (diagU i s hs : Matrix (Fin m) (Fin m) K) *
      (((diagU i s hs)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 :=
    Units.mul_inv (diagU i s hs)
  have key : (diagU i s hs : Matrix (Fin m) (Fin m) K) * Matrix.single i j 1 *
      (((diagU i s hs)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        s • Matrix.single i j 1 := by
    rw [diagU_val, diagU_inv_val, diagonal_mul_single_mul_diagonal, smul_single_one]
    have hj : j ≠ i := Ne.symm hij
    simp [hj]
  have hee : Matrix.single i j (1 : K) * Matrix.single i j 1 = 0 := by
    simp [Ne.symm hij]
  rw [transU_val, transU_inv_val]
  calc (diagU i s hs : Matrix (Fin m) (Fin m) K) * (1 + Matrix.single i j 1) *
        (((diagU i s hs)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
          (1 - Matrix.single i j 1)
      = ((diagU i s hs : Matrix (Fin m) (Fin m) K) *
          (((diagU i s hs)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) +
          (diagU i s hs : Matrix (Fin m) (Fin m) K) * Matrix.single i j 1 *
            (((diagU i s hs)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) *
          (1 - Matrix.single i j 1) := by
        noncomm_ring
    _ = (1 + s • Matrix.single i j 1) * (1 - Matrix.single i j 1) := by
        rw [hDD, key]
    _ = 1 + (s - 1) • Matrix.single i j 1 := by
        simp only [add_mul, one_mul, smul_mul_assoc, mul_sub, mul_one, hee, smul_zero, sub_zero,
          sub_smul, one_smul]
        abel

theorem altT_mul_row (i j : Fin m) (hij : i ≠ j) (t : K) (M : Matrix (Fin m) (Fin m) K)
    (l : Fin m) : (altT i j t * M) i l = t * M j l ∧ (altT i j t * M) j l = t * M i l := by
  have hji : j ≠ i := Ne.symm hij
  constructor
  · simp [altT, add_mul, Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne, hij, hji]
  · simp [altT, add_mul, Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne, hij, hji]

theorem mul_altT_col (i j : Fin m) (hij : i ≠ j) (t : K) (M : Matrix (Fin m) (Fin m) K)
    (k : Fin m) : (M * altT i j t) k j = M k i * t ∧ (M * altT i j t) k i = M k j * t := by
  have hji : j ≠ i := Ne.symm hij
  constructor
  · simp [altT, mul_add, Matrix.mul_single_apply_same, Matrix.mul_single_apply_of_ne, hij, hji]
  · simp [altT, mul_add, Matrix.mul_single_apply_same, Matrix.mul_single_apply_of_ne, hij, hji]

theorem altT_apply_row_second {r q : Fin m} (hrq : r ≠ q) (t : K) (l : Fin m) :
    altT r q t q l = if l = r then t else 0 := by
  simp [altT, Matrix.single_apply, hrq, Ne.symm hrq, eq_comm]

theorem exists_ne_index (hm : 2 ≤ m) (r : Fin m) : ∃ j : Fin m, j ≠ r := by
  have hm1 : 1 < Fintype.card (Fin m) := by simp; omega
  exact Fintype.exists_ne_of_one_lt_card hm1 r

theorem commutator_diag_upU (i j : Fin m) (hij : i ≠ j) (s : K) (hs : s ≠ 0) :
    (⁅levU (diagU i s hs), upU (altT i j 1)⁆ : GL (Fin m ⊕ Fin m) K).val =
      fromBlocks 1 (altT i j (s - 1)) 0 1 := by
  have hX : -altT i j 1 + altT i j (s * 1) = altT i j (s - 1) := by
    rw [altT_eq_smul i j (s * 1), altT_eq_smul i j (s - 1)]
    module
  rw [commutator_levU_upU_val, diagU_mul_altT_mul_transpose i j hij s hs 1, hX]

theorem commutator_diag_lowU (i j : Fin m) (hij : i ≠ j) (s : K) (hs : s ≠ 0) :
    (⁅levU (diagU i s hs), lowU (altT i j 1)⁆ : GL (Fin m ⊕ Fin m) K).val =
      fromBlocks 1 0 (altT i j (s⁻¹ - 1)) 1 := by
  have hX : altT i j (s⁻¹ * 1) - altT i j 1 = altT i j (s⁻¹ - 1) := by
    rw [altT_eq_smul i j (s⁻¹ * 1), altT_eq_smul i j (s⁻¹ - 1)]
    module
  rw [commutator_levU_lowU_val, diagU_inv_mul_altT_mul i j hij s hs 1, hX]

theorem mem_statedOmega_comm {g h : GL (Fin m ⊕ Fin m) K}
    (hg : ∀ v, StatedQuadPlus m K ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) =
      StatedQuadPlus m K v)
    (hh : ∀ v, StatedQuadPlus m K ((h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) =
      StatedQuadPlus m K v) :
    ⁅g, h⁆ ∈ StatedOmega (StatedQuadPlus m K) :=
  Subgroup.commutator_mem_commutator (Subgroup.subset_closure hg) (Subgroup.subset_closure hh)

theorem toMatrix_comm_of_mulVec {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → K) →ₗ[K] (ι → K)) (M : Matrix ι ι K) (h : ∀ v, f (M *ᵥ v) = M *ᵥ f v) :
    LinearMap.toMatrix' f * M = M * LinearMap.toMatrix' f := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec,
    LinearMap.toMatrix'_mulVec]
  exact h _

theorem exists_ne_zero_ne_one (F : Type) [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ s : F, s ≠ 0 ∧ s ≠ 1 := by
  classical
  by_contra H
  have H' : ∀ x : F, x ≠ 0 → x = 1 := fun x hx => by
    by_contra h1
    exact H ⟨x, hx, h1⟩
  haveI := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ ({0, 1} : Finset F) := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [H' x hx]
  have h1 := Finset.card_le_card hsub
  have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  omega

theorem scalar_of_commute (hm : 2 ≤ m) {a b c d : Matrix (Fin m) (Fin m) K} {t₁ t₂ t₃ : K}
    (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (ht₃ : t₃ ≠ 0)
    (hU : ∀ i j : Fin m, i ≠ j → a * altT i j t₁ = altT i j t₁ * d ∧ altT i j t₁ * c = 0)
    (hL : ∀ i j : Fin m, i ≠ j → b * altT i j t₂ = 0)
    (hE : ∀ i j : Fin m, i ≠ j →
      a * (1 + t₃ • Matrix.single i j 1) = (1 + t₃ • Matrix.single i j 1) * a) :
    ∃ l : K, a = l • 1 ∧ b = 0 ∧ c = 0 ∧ d = l • 1 := by
  have hc : c = 0 := by
    ext r l
    obtain ⟨j, hj⟩ := exists_ne_index hm r
    have h := congrFun (congrFun (hU r j hj.symm).2 j) l
    rw [(altT_mul_row r j hj.symm t₁ c l).2] at h
    simpa [ht₁] using h
  have hb : b = 0 := by
    ext k r
    obtain ⟨j, hj⟩ := exists_ne_index hm r
    have h := congrFun (congrFun (hL r j hj.symm) k) j
    rw [(mul_altT_col r j hj.symm t₂ b k).1] at h
    simpa [ht₂] using h
  have hae : ∀ i j : Fin m, i ≠ j → a * Matrix.single i j 1 = Matrix.single i j 1 * a := by
    intro i j hij
    have h := hE i j hij
    rw [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc] at h
    exact smul_right_injective _ ht₃ (add_left_cancel h)
  have hcol : ∀ i k : Fin m, k ≠ i → a k i = 0 := by
    intro i k hki
    obtain ⟨j, hj⟩ := exists_ne_index hm i
    have h := congrFun (congrFun (hae i j hj.symm) k) j
    rw [Matrix.mul_single_apply_same] at h
    simpa [hki] using h
  have hdiag : ∀ i j : Fin m, i ≠ j → a i i = a j j := by
    intro i j hij
    have h := congrFun (congrFun (hae i j hij) i) j
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at h
    simpa using h
  obtain ⟨l, ha⟩ : ∃ l : K, a = l • 1 := by
    obtain ⟨i0⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    refine ⟨a i0 i0, ?_⟩
    ext r x
    by_cases hrx : r = x
    · subst hrx
      by_cases hr0 : r = i0
      · subst hr0
        simp
      · simp [hdiag r i0 hr0]
    · simp [hrx, hcol x r hrx]
  refine ⟨l, ha, hb, hc, ?_⟩
  ext r x
  obtain ⟨q, hq⟩ := exists_ne_index hm r
  have h := congrFun (congrFun (hU r q hq.symm).1 q) x
  rw [ha, smul_mul, one_mul, Matrix.smul_apply, (altT_mul_row r q hq.symm t₁ d x).2,
    altT_apply_row_second hq.symm t₁ x, smul_eq_mul] at h
  by_cases hxr : x = r
  · subst hxr
    simp only [if_true] at h
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact mul_left_cancel₀ ht₁ (by rw [← h]; ring)
  · simp only [hxr, if_false, mul_zero] at h
    rw [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hxr), smul_eq_mul, mul_zero]
    exact (mul_eq_zero.mp h.symm).resolve_left ht₁

theorem stroth_2_4_omegaPlus (K : Type) [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (m : ℕ) (hm : 2 ≤ m)
    (f : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))
    (hf : ∀ A ∈ StatedOmega (StatedQuadPlus m K),
      ∀ v, f ((A : Matrix _ _ K) *ᵥ v) = (A : Matrix _ _ K) *ᵥ f v) :
    ∃ c : K, ∀ v, f v = c • v := by
  obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one K hK
  have hcomm : ∀ g ∈ StatedOmega (StatedQuadPlus m K),
      LinearMap.toMatrix' f * (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * LinearMap.toMatrix' f :=
    fun g hg => toMatrix_comm_of_mulVec f _ (hf g hg)
  obtain ⟨a, b, c, d, hFabcd⟩ : ∃ a b c d : Matrix (Fin m) (Fin m) K,
      LinearMap.toMatrix' f = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks (LinearMap.toMatrix' f)).symm⟩
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs2' : s⁻¹ - 1 ≠ 0 := by
    intro h
    apply hs1
    have h' : s⁻¹ = 1 := sub_eq_zero.mp h
    simpa using h'
  have hU : ∀ i j : Fin m, i ≠ j →
      a * altT i j (s - 1) = altT i j (s - 1) * d ∧ altT i j (s - 1) * c = 0 := by
    intro i j hij
    have h := hcomm _ (mem_statedOmega_comm (statedQuadPlus_levU (diagU i s hs0))
      (statedQuadPlus_upU hij 1))
    rw [commutator_diag_upU i j hij s hs0, hFabcd, fromBlocks_multiply, fromBlocks_multiply,
      fromBlocks_inj] at h
    obtain ⟨h1, h2, -, -⟩ := h
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
      zero_add] at h1 h2
    refine ⟨add_right_cancel (h2.trans (add_comm _ _)), ?_⟩
    simpa using h1.symm
  have hL : ∀ i j : Fin m, i ≠ j → b * altT i j (s⁻¹ - 1) = 0 := by
    intro i j hij
    have h := hcomm _ (mem_statedOmega_comm (statedQuadPlus_levU (diagU i s hs0))
      (statedQuadPlus_lowU hij 1))
    rw [commutator_diag_lowU i j hij s hs0, hFabcd, fromBlocks_multiply, fromBlocks_multiply,
      fromBlocks_inj] at h
    obtain ⟨h1, -, -, -⟩ := h
    simpa using h1
  have hE : ∀ i j : Fin m, i ≠ j →
      a * (1 + (s - 1) • Matrix.single i j 1) = (1 + (s - 1) • Matrix.single i j 1) * a := by
    intro i j hij
    have h := hcomm _ (mem_statedOmega_comm (statedQuadPlus_levU (diagU i s hs0))
      (statedQuadPlus_levU (transU (K := K) i j hij)))
    rw [commutator_levU_levU_val, diagU_mul_transU_mul_inv i j hij s hs0, hFabcd,
      fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
    obtain ⟨h1, -, -, -⟩ := h
    simpa using h1
  obtain ⟨l, ha, hb, hc, hd⟩ := scalar_of_commute hm hs1' hs2' hs1' hU hL hE
  have hF : LinearMap.toMatrix' f = l • 1 := by
    rw [hFabcd, ha, hb, hc, hd]
    ext x y
    rcases x with x | x <;> rcases y with y | y <;> simp [Matrix.one_apply]
  refine ⟨l, fun v => ?_⟩
  rw [← LinearMap.toMatrix'_mulVec f v, hF, Matrix.smul_mulVec, Matrix.one_mulVec]

end CFSG.RankThree.GF2n.Stroth80

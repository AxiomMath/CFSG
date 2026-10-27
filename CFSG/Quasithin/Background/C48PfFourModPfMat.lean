module

public import CFSG.Quasithin.Background.C48PfFourModPfGrp
public import CFSG.Quasithin.Background.F918T0
public import CFSG.Quasithin.Background.F918F2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C48Pf.FMod

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L

variable {n : ℕ}

@[expose] def restrictBlk (a m : ℕ) (h : a + m ≤ n) (w : Fin n → ZMod 2) : Fin m → ZMod 2 :=
  fun j => w ⟨a + j, by have := j.isLt; omega⟩

theorem transvection_mulVec_eq_self_iff {k l : Fin n} (w : Fin n → ZMod 2) :
    (1 + Matrix.single k l (1 : ZMod 2)) *ᵥ w = w ↔ w l = 0 := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, one_mul]
  constructor
  · intro h
    have := congrFun h k
    simpa using this
  · intro h
    rw [h]
    simp

theorem mulVec_eq_self_of_blockForm {a m : ℕ} {t : Matrix (Fin n) (Fin n) (ZMod 2)}
    (ht : BlockForm a m t) {w : Fin n → ZMod 2} (hw : ∀ j : Fin n, a ≤ (j : ℕ) → w j = 0) :
    t *ᵥ w = w := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hi : (i : ℕ) < a
    · rw [ht.2.2.1 i i hi hi, ite_eq_left rfl, one_mul]
    · rw [hw i (by omega), mul_zero]
  · intro j _ hji
    by_cases hj : (j : ℕ) < a
    · by_cases hi : (i : ℕ) < a
      · rw [ht.2.2.1 i j hi hj, ite_eq_right (Ne.symm hji), zero_mul]
      · rw [ht.1 i j (by omega) hj, zero_mul]
    · rw [hw j (by omega), mul_zero]
  · simp

theorem mulVec_of_blockForm_blk {a m : ℕ} (h : a + m ≤ n) {t : Matrix (Fin n) (Fin n) (ZMod 2)}
    (ht : BlockForm a m t) {w : Fin n → ZMod 2}
    (hw : ∀ j : Fin n, ((j : ℕ) < a ∨ a + m ≤ (j : ℕ)) → w j = 0) :
    (∀ j : Fin n, a + m ≤ (j : ℕ) → (t *ᵥ w) j = 0) ∧
      restrictBlk a m h (t *ᵥ w) = blkAt a m h t *ᵥ restrictBlk a m h w := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < a + m
    · by_cases hj' : (j : ℕ) < a
      · rw [hw j (Or.inl hj'), mul_zero]
      · rw [ht.2.1 i j hi hj, zero_mul]
    · rw [hw j (Or.inr (by omega)), mul_zero]
  · funext i
    simp only [restrictBlk, Matrix.mulVec, dotProduct, blkAt_apply]
    exact sum_block h _ fun k hk => by rw [hw k hk, mul_zero]

theorem transvection_dual_mulVec_eq_self_iff {k l : Fin n} (hkl : k ≠ l) (w : Fin n → ZMod 2) :
    (((SpecialLinearGroup.transvection hkl (1 : ZMod 2))⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ w = w ↔ w k = 0 := by
  rw [SpecialLinearGroup.transvection_inv, CFSG.LinearGroups.coe_transvection,
    Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  constructor
  · intro h
    have := congrFun h l
    simpa using this
  · intro h
    rw [h]
    simp

theorem transpose_mulVec_eq_self_of_blockForm {a m : ℕ} {s : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hs : BlockForm a m s) {w : Fin n → ZMod 2}
    (hw : ∀ j : Fin n, (j : ℕ) < a + m → w j = 0) : sᵀ *ᵥ w = w := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hi : a + m ≤ (i : ℕ)
    · rw [hs.2.2.2 i i hi hi, ite_eq_left rfl, one_mul]
    · rw [hw i (by omega), mul_zero]
  · intro j _ hji
    by_cases hj : a + m ≤ (j : ℕ)
    · by_cases hi : a + m ≤ (i : ℕ)
      · rw [hs.2.2.2 j i hj hi, ite_eq_right hji, zero_mul]
      · rw [hs.2.1 j i hj (by omega), zero_mul]
    · rw [hw j (by omega), mul_zero]
  · simp

theorem transpose_mulVec_of_blockForm_blk {a m : ℕ} (h : a + m ≤ n)
    {s : Matrix (Fin n) (Fin n) (ZMod 2)} (hs : BlockForm a m s) {w : Fin n → ZMod 2}
    (hw : ∀ j : Fin n, ((j : ℕ) < a ∨ a + m ≤ (j : ℕ)) → w j = 0) :
    (∀ j : Fin n, (j : ℕ) < a → (sᵀ *ᵥ w) j = 0) ∧
      restrictBlk a m h (sᵀ *ᵥ w) = (blkAt a m h s)ᵀ *ᵥ restrictBlk a m h w := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : a ≤ (j : ℕ)
    · by_cases hj' : (j : ℕ) < a + m
      · rw [hs.1 j i hj hi, zero_mul]
      · rw [hw j (Or.inr (by omega)), mul_zero]
    · rw [hw j (Or.inl (by omega)), mul_zero]
  · funext i
    simp only [restrictBlk, Matrix.mulVec, dotProduct, blkAt_apply, Matrix.transpose_apply]
    exact sum_block h _ fun k hk => by rw [hw k hk, mul_zero]

theorem alt_row_eq_zero_of_transvection {k l : Fin n}
    {M : Matrix (Fin n) (Fin n) (ZMod 2)} (hfix : (1 + Matrix.single k l (1 : ZMod 2)) * M *
      (1 + Matrix.single k l (1 : ZMod 2))ᵀ = M) {j : Fin n} (hj : j ≠ k) : M l j = 0 := by
  have h1 := congrFun (congrFun hfix k) j
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single, Matrix.mul_add,
    Matrix.mul_one, Matrix.add_apply, Matrix.mul_single_apply_of_ne _ _ _ _ _ hj, add_zero,
    Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.single_mul_apply_same,
    one_mul] at h1
  simpa using h1

theorem alt_symm {M : Matrix (Fin n) (Fin n) (ZMod 2)} (hM : M ∈ altMat n) (i j : Fin n) :
    M j i = M i j := by
  have := congrFun (congrFun hM.1 i) j
  simpa using this

theorem alt_row_eq_zero_of_two {k k' l : Fin n} (hk : k ≠ k')
    {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h1 : (1 + Matrix.single k l (1 : ZMod 2)) * M * (1 + Matrix.single k l (1 : ZMod 2))ᵀ = M)
    (h2 : (1 + Matrix.single k' l (1 : ZMod 2)) * M * (1 + Matrix.single k' l (1 : ZMod 2))ᵀ =
      M) (j : Fin n) : M l j = 0 := by
  by_cases hj : j = k
  · exact alt_row_eq_zero_of_transvection h2 (by rw [hj]; exact hk)
  · exact alt_row_eq_zero_of_transvection h1 hj

abbrev tvM (k l : Fin n) : Matrix (Fin n) (Fin n) (ZMod 2) := 1 + Matrix.single k l 1

theorem alt_support_zero {m : ℕ} (hm2 : 2 ≤ m) {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : M ∈ altMat n)
    (hfix : ∀ k l : Fin n, IsCross 0 m k l → tvM k l * M * (tvM k l)ᵀ = M) (i j : Fin n)
    (hij : m ≤ (i : ℕ) ∨ m ≤ (j : ℕ)) : M i j = 0 := by
  have hrow : ∀ l : Fin n, m ≤ (l : ℕ) → ∀ j, M l j = 0 := by
    intro l hl j
    have hn : m ≤ n := by have := l.isLt; omega
    refine alt_row_eq_zero_of_two (k := ⟨0, by omega⟩) (k' := ⟨1, by omega⟩) (by simp)
      (hfix _ _ (Or.inr ⟨by simp, by simp; omega, by simpa using hl⟩))
      (hfix _ _ (Or.inr ⟨by simp, by simp; omega, by simpa using hl⟩)) j
  rcases hij with hi | hj
  · exact hrow i hi j
  · rw [← alt_symm hM]
    exact hrow j hj i

theorem alt_support_one {m : ℕ} (hm2 : 2 ≤ m) {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : M ∈ altMat n)
    (hfix : ∀ k l : Fin n, IsCross 1 m k l → tvM k l * M * (tvM k l)ᵀ = M) (i j : Fin n)
    (hij : ¬ (((i : ℕ) = 0 ∧ 1 ≤ (j : ℕ) ∧ (j : ℕ) < 1 + m) ∨
      ((j : ℕ) = 0 ∧ 1 ≤ (i : ℕ) ∧ (i : ℕ) < 1 + m))) : M i j = 0 := by
  have hrowC : ∀ l : Fin n, 1 + m ≤ (l : ℕ) → ∀ j, M l j = 0 := by
    intro l hl j
    refine alt_row_eq_zero_of_two (k := ⟨1, by omega⟩) (k' := ⟨2, by omega⟩) (by simp)
      (hfix _ _ (Or.inr ⟨by simp, by simp; omega, by simpa using hl⟩))
      (hfix _ _ (Or.inr ⟨by simp, by simp; omega, by simpa using hl⟩)) j
  have hrowB : ∀ l : Fin n, 1 ≤ (l : ℕ) → (l : ℕ) < 1 + m → ∀ j : Fin n, (j : ℕ) ≠ 0 →
      M l j = 0 := by
    intro l hl1 hl2 j hj
    refine alt_row_eq_zero_of_transvection (k := ⟨0, by omega⟩)
      (hfix _ _ (Or.inl ⟨by simp, hl1, hl2⟩)) ?_
    intro e
    exact hj (by rw [e])
  by_cases hi0 : (i : ℕ) = 0
  · by_cases hj0 : (j : ℕ) = 0
    · have : i = j := Fin.ext (by omega)
      rw [this]
      exact hM.2 j
    · by_cases hjB : (j : ℕ) < 1 + m
      · exact absurd (Or.inl ⟨hi0, by omega, hjB⟩) hij
      · rw [← alt_symm hM]
        exact hrowC j (by omega) i
  · by_cases hiB : (i : ℕ) < 1 + m
    · by_cases hj0 : (j : ℕ) = 0
      · exact absurd (Or.inr ⟨hj0, by omega, hiB⟩) hij
      · exact hrowB i (by omega) hiB j hj0
    · exact hrowC i (by omega) j

theorem alt_support_two {m : ℕ} (hm2 : 2 ≤ m) {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : M ∈ altMat n)
    (hfix : ∀ k l : Fin n, IsCross 2 m k l → tvM k l * M * (tvM k l)ᵀ = M) (i j : Fin n)
    (hij : 2 ≤ (i : ℕ) ∨ 2 ≤ (j : ℕ)) : M i j = 0 := by
  have hrow : ∀ l : Fin n, 2 ≤ (l : ℕ) → ∀ j, M l j = 0 := by
    intro l hl j
    by_cases hlB : (l : ℕ) < 2 + m
    · exact alt_row_eq_zero_of_two (k := ⟨0, by omega⟩) (k' := ⟨1, by omega⟩) (by simp)
        (hfix _ _ (Or.inl ⟨by simp, hl, hlB⟩)) (hfix _ _ (Or.inl ⟨by simp, hl, hlB⟩)) j
    · exact alt_row_eq_zero_of_two (k := ⟨2, by omega⟩) (k' := ⟨3, by omega⟩) (by simp)
        (hfix _ _ (Or.inr ⟨by simp, by simp; omega, by omega⟩))
        (hfix _ _ (Or.inr ⟨by simp, by simp; omega, by omega⟩)) j
  rcases hij with hi | hj
  · exact hrow i hi j
  · rw [← alt_symm hM]
    exact hrow j hj i

theorem blkAt_congr_of_support {m : ℕ} (h : 0 + m ≤ n) (t : Matrix (Fin n) (Fin n) (ZMod 2))
    {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : ∀ i j : Fin n, (m ≤ (i : ℕ) ∨ m ≤ (j : ℕ)) → M i j = 0) :
    blkAt 0 m h (t * M * tᵀ) = blkAt 0 m h t * blkAt 0 m h M * (blkAt 0 m h t)ᵀ := by
  ext i j
  simp only [blkAt_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [sum_block h]
  · refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    rw [sum_block h]
    intro p hp
    rw [hM p _ (Or.inl (by omega)), mul_zero]
  · intro q hq
    have : ∀ p : Fin n, M p q = 0 := fun p => hM p q (Or.inr (by omega))
    simp [this]

theorem col_congr_of_support {m : ℕ} (h : 1 + m ≤ n) {t : Matrix (Fin n) (Fin n) (ZMod 2)}
    (ht : BlockForm 1 m t) {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : ∀ i j : Fin n, ¬ (((i : ℕ) = 0 ∧ 1 ≤ (j : ℕ) ∧ (j : ℕ) < 1 + m) ∨
      ((j : ℕ) = 0 ∧ 1 ≤ (i : ℕ) ∧ (i : ℕ) < 1 + m)) → M i j = 0) :
    (fun j : Fin m => (t * M * tᵀ) ⟨1 + j, by have := j.isLt; omega⟩ ⟨0, by omega⟩) =
      blkAt 1 m h t *ᵥ fun j : Fin m => M ⟨1 + j, by have := j.isLt; omega⟩ ⟨0, by omega⟩ := by
  funext i
  have ht00 : t ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
    rw [ht.2.2.1 _ _ (by simp) (by simp)]
    simp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, blkAt_apply]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
  · rw [ht00, mul_one]
    rw [sum_block h]
    intro p hp
    rw [hM p _ (by
      rintro (⟨-, h2, -⟩ | ⟨-, h2, h3⟩)
      · simp at h2
      · rcases hp with hp | hp <;> omega), mul_zero]
  · intro q _ hq
    have hq' : (q : ℕ) ≠ 0 := fun e => hq (Fin.ext e)
    have hrow : ∀ p : Fin n, t ⟨1 + i, by have := i.isLt; omega⟩ p * M p q = 0 := by
      intro p
      by_cases hp0 : (p : ℕ) = 0
      · rw [ht.1 _ _ (by simp) (by omega), zero_mul]
      · rw [hM p q (by
          rintro (⟨h1, -⟩ | ⟨h1, -⟩)
          · exact hp0 h1
          · exact hq' h1), mul_zero]
    simp [hrow]
  · simp

theorem congr_eq_self_of_support_two {m : ℕ} {t : Matrix (Fin n) (Fin n) (ZMod 2)}
    (ht : BlockForm 2 m t) {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : ∀ i j : Fin n, (2 ≤ (i : ℕ) ∨ 2 ≤ (j : ℕ)) → M i j = 0) : t * M * tᵀ = M := by
  have hcol : ∀ (i p : Fin n), (p : ℕ) < 2 → t i p = if i = p then 1 else 0 := by
    intro i p hp
    by_cases hi : (i : ℕ) < 2
    · exact ht.2.2.1 i p hi hp
    · rw [ht.1 i p (by omega) hp, ite_eq_right (fun e => hi (by rw [e]; exact hp))]
  ext i j
  have hterm : ∀ q p : Fin n, t i p * M p q * t j q =
      (if i = p then 1 else 0) * M p q * (if j = q then 1 else 0) := by
    intro q p
    by_cases hp : (p : ℕ) < 2
    · by_cases hq : (q : ℕ) < 2
      · rw [hcol i p hp, hcol j q hq]
      · rw [hM p q (Or.inr (by omega))]
        simp
    · rw [hM p q (Or.inl (by omega))]
      simp
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, hterm]
  simp [ite_mul, mul_ite, Finset.sum_ite_eq]

@[expose] def altVec3 (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Fin 3 → ZMod 2 :=
  ![N 1 2, N 0 2, N 0 1]

theorem alt3_eq {N : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hN : N ∈ altMat 3) :
    N = !![0, N 0 1, N 0 2; N 0 1, 0, N 1 2; N 0 2, N 1 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first | exact hN.2 _ | rfl | exact alt_symm hN _ _

theorem alt4_eq {N : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hN : N ∈ altMat 4) :
    N = !![0, N 0 1, N 0 2, N 0 3; N 0 1, 0, N 1 2, N 1 3; N 0 2, N 1 2, 0, N 2 3;
      N 0 3, N 1 3, N 2 3, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first | exact hN.2 _ | rfl | exact alt_symm hN _ _

@[expose] def altCoords4 (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Fin 6 → ZMod 2 :=
  fun k => N (pr4' k).1 (pr4' k).2

theorem altCoords4_congr (g : Matrix (Fin 4) (Fin 4) (ZMod 2))
    {N : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hN : N ∈ altMat 4) :
    altCoords4 (g * N * gᵀ) = minors4 g *ᵥ altCoords4 N := by
  rw [alt4_eq hN]
  ext k
  fin_cases k <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp [altCoords4, pr4', minors4, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mulVec,
      dotProduct, Fin.sum_univ_six]
    simp only [CharTwo.sub_eq_add]
    ring

end CFSG.Quasithin.C48Pf.FMod

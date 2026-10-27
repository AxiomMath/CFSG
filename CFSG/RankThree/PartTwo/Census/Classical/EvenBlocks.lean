module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartTwo.Census

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven

section Reindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (K : Type*)
  [CommRing K]

@[expose] noncomputable def slReindex (e : ι ≃ κ) :
    SpecialLinearGroup ι K ≃* SpecialLinearGroup κ K where
  toFun A := ⟨reindex e e (A : Matrix ι ι K), by rw [det_reindex_self]; exact A.2⟩
  invFun A := ⟨reindex e.symm e.symm (A : Matrix κ κ K), by rw [det_reindex_self]; exact A.2⟩
  left_inv A := Subtype.ext (by simp)
  right_inv A := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    change reindex e e ((A : Matrix ι ι K) * (B : Matrix ι ι K)) =
      reindex e e (A : Matrix ι ι K) * reindex e e (B : Matrix ι ι K)
    simp [reindex_apply, submatrix_mul_equiv])

@[expose] noncomputable def pslReindex (e : ι ≃ κ) :
    ProjectiveSpecialLinearGroup ι K ≃* ProjectiveSpecialLinearGroup κ K :=
  QuotientGroup.congr _ _ (slReindex K e) (Subgroup.map_center_eq _)

end Reindex

section Blocks

variable {K : Type} [Field K] [CharP K 2]

@[expose] def threeCycleMat (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 1]

theorem threeCycleMat_sq : threeCycleMat K ^ 2 = !![1, 1; 1, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pow_two, threeCycleMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination h2

theorem threeCycleMat_pow_three : threeCycleMat K ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pow_succ, threeCycleMat_sq, threeCycleMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination h2

theorem det_threeCycleMat : (threeCycleMat K).det = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [threeCycleMat, det_fin_two_of]
  linear_combination -h2

theorem threeCycleMat_pow_val_add (x y : ZMod 3) :
    threeCycleMat K ^ (x + y).val = threeCycleMat K ^ x.val * threeCycleMat K ^ y.val := by
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ threeCycleMat_pow_three]

theorem threeCycleMat_pow_val_zero_one {x : ZMod 3} (hx : (threeCycleMat K ^ x.val) 0 1 = 0) :
    x = 0 := by
  fin_cases x
  · rfl
  · exfalso
    change (threeCycleMat K ^ 1) 0 1 = 0 at hx
    simp [threeCycleMat] at hx
  · exfalso
    change (threeCycleMat K ^ 2) 0 1 = 0 at hx
    simp [threeCycleMat_sq] at hx

@[expose] def sBlockMat (a : Fin 4 → ZMod 3) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) K :=
  blockDiagonal fun b => threeCycleMat K ^ (a b).val

theorem sBlockMat_add (a a' : Fin 4 → ZMod 3) :
    sBlockMat (K := K) (a + a') = sBlockMat a * sBlockMat a' := by
  rw [sBlockMat, sBlockMat, sBlockMat, ← blockDiagonal_mul]
  congr 1
  funext b
  rw [Pi.add_apply, threeCycleMat_pow_val_add]

theorem det_sBlockMat (a : Fin 4 → ZMod 3) : (sBlockMat (K := K) a).det = 1 := by
  rw [sBlockMat, det_blockDiagonal]
  exact Finset.prod_eq_one fun b _ => by rw [det_pow, det_threeCycleMat, one_pow]

abbrev BlockIdx (m : ℕ) : Type := (Fin 2 × Fin 4) ⊕ Fin m

@[expose] def sHom (m : ℕ) (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Fin 4 → ZMod 3) →* SpecialLinearGroup (BlockIdx m) K where
  toFun a := ⟨fromBlocks (sBlockMat a.toAdd) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, det_sBlockMat, det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    change fromBlocks (sBlockMat (0 : Fin 4 → ZMod 3)) 0 0 1 = (1 : Matrix (BlockIdx m) _ K)
    rw [← fromBlocks_one, sBlockMat]
    congr 1
    rw [← blockDiagonal_one]
    congr 1)
  map_mul' a b := Subtype.ext (by
    change fromBlocks (sBlockMat (a.toAdd + b.toAdd)) 0 0 1 =
      fromBlocks (sBlockMat (K := K) a.toAdd) 0 0 1 * fromBlocks (sBlockMat b.toAdd) 0 0 1
    rw [fromBlocks_multiply, sBlockMat_add]
    simp)

theorem coe_sHom (m : ℕ) (a : Multiplicative (Fin 4 → ZMod 3)) :
    ((sHom m K a : SpecialLinearGroup (BlockIdx m) K) : Matrix (BlockIdx m) (BlockIdx m) K) =
      fromBlocks (sBlockMat a.toAdd) 0 0 1 :=
  rfl

@[expose] def yMat (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) K :=
  Matrix.of fun ib jb => if ib.2 = 0 ∧ jb.2 = 1 then X ib.1 jb.1 else 0

omit [CharP K 2] in
theorem yMat_mul_yMat (X X' : Matrix (Fin 2) (Fin 2) K) : yMat X * yMat X' = 0 := by
  ext ib jb
  simp only [mul_apply, yMat, of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun kc _ => ?_
  by_cases h : kc.2 = 1
  · have : ¬ (kc.2 = 0 ∧ jb.2 = 1) := fun h' => by rw [h] at h'; exact absurd h'.1 (by decide)
    rw [ite_eq_right this, mul_zero]
  · have : ¬ (ib.2 = 0 ∧ kc.2 = 1) := fun h' => h h'.2
    rw [ite_eq_right this, zero_mul]

omit [CharP K 2] in
theorem yMat_zero : yMat (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext ib jb
  simp [yMat]

omit [CharP K 2] in
theorem yMat_add (X X' : Matrix (Fin 2) (Fin 2) K) : yMat (X + X') = yMat X + yMat X' := by
  ext ib jb
  simp only [yMat, of_apply, Matrix.add_apply]
  split_ifs <;> simp

omit [CharP K 2] in
theorem one_add_yMat_mul (X X' : Matrix (Fin 2) (Fin 2) K) :
    (1 + yMat X) * (1 + yMat X') = 1 + yMat (X + X') := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, yMat_mul_yMat, add_zero, yMat_add]
  abel

theorem det_one_add_yMat (X : Matrix (Fin 2) (Fin 2) K) : (1 + yMat X).det = 1 := by
  have hX : X + X = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
  refine eq_one_of_mul_self_eq_one ?_
  rw [← det_mul, one_add_yMat_mul, hX, yMat_zero, add_zero, det_one]

@[expose] def uHom (m : ℕ) (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Matrix (Fin 2) (Fin 2) K) →* SpecialLinearGroup (BlockIdx m) K where
  toFun X := ⟨fromBlocks (1 + yMat X.toAdd) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, det_one_add_yMat, det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    change fromBlocks (1 + yMat (0 : Matrix (Fin 2) (Fin 2) K)) 0 0 1 =
      (1 : Matrix (BlockIdx m) _ K)
    rw [← fromBlocks_one, yMat_zero, add_zero])
  map_mul' X X' := Subtype.ext (by
    change fromBlocks (1 + yMat (X.toAdd + X'.toAdd)) 0 0 1 =
      fromBlocks (1 + yMat (K := K) X.toAdd) 0 0 1 * fromBlocks (1 + yMat X'.toAdd) 0 0 1
    rw [fromBlocks_multiply, one_add_yMat_mul]
    simp)

theorem sBlockMat_mul_yMat (a : Fin 4 → ZMod 3) (X : Matrix (Fin 2) (Fin 2) K) :
    sBlockMat a * yMat X =
      yMat (threeCycleMat K ^ (a 0).val * X * threeCycleMat K ^ (-(a 1)).val) * sBlockMat a := by
  set X' := threeCycleMat K ^ (a 0).val * X * threeCycleMat K ^ (-(a 1)).val with hX'
  have key : threeCycleMat K ^ (a 0).val * X = X' * threeCycleMat K ^ (a 1).val := by
    rw [hX', mul_assoc _ (threeCycleMat K ^ (-(a 1)).val), ← threeCycleMat_pow_val_add,
      show -(a 1) + a 1 = 0 from neg_add_cancel _, ZMod.val_zero, pow_zero, mul_one]
  ext ⟨i, b⟩ ⟨j, b'⟩
  simp only [mul_apply, Fintype.sum_prod_type, sBlockMat, blockDiagonal_apply, yMat, of_apply]
  by_cases h : b = 0 ∧ b' = 1
  · obtain ⟨rfl, rfl⟩ := h
    have := congrFun (congrFun key i) j
    simp only [mul_apply] at this
    simpa [ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
  · have h1 : ∀ k c, (if b = c then (threeCycleMat K ^ (a b).val) i k else 0) *
        (if c = 0 ∧ b' = 1 then X k j else 0) = 0 := by
      intro k c
      by_cases hbc : b = c
      · subst hbc
        rw [ite_eq_right h, mul_zero]
      · rw [ite_eq_right hbc, zero_mul]
    have h2 : ∀ k c, (if b = 0 ∧ c = 1 then X' i k else 0) *
        (if c = b' then (threeCycleMat K ^ (a c).val) k j else 0) = 0 := by
      intro k c
      by_cases hc : c = b'
      · subst hc
        rw [ite_eq_right h, zero_mul]
      · rw [ite_eq_right hc, mul_zero]
    simp only [h1, h2, Finset.sum_const_zero]

theorem eq_one_of_sHom_entry {m : ℕ} {a : Multiplicative (Fin 4 → ZMod 3)}
    (h : ∀ b : Fin 4, ((sHom m K a : SpecialLinearGroup (BlockIdx m) K) :
      Matrix (BlockIdx m) (BlockIdx m) K) (.inl (0, b)) (.inl (1, b)) = 0) : a = 1 := by
  apply Multiplicative.toAdd.injective
  funext b
  have hb := h b
  rw [coe_sHom, fromBlocks_apply₁₁, sBlockMat, blockDiagonal_apply] at hb
  simp only [ite_true] at hb
  exact threeCycleMat_pow_val_zero_one hb

theorem four_le_localRank_PSL_blocks [Finite K] (m : ℕ) :
    4 ≤ localRank 3 (ProjectiveSpecialLinearGroup (BlockIdx m) K) := by
  set φ := sHom m K
  set ψ := uHom m K
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr fun a ha =>
      eq_one_of_sHom_entry (K := K) (m := m) fun b => ?_
    rw [ha]
    simp
  refine le_localRank_quotient_of_le_normalizer _ Nat.prime_three (E := φ.range) (P := ψ.range)
    (isElemAbelian_range (fun a => ?_) φ) ?_ ?_ ?_ ?_ ?_
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext b
    change 3 • (Multiplicative.toAdd a b) = 0
    generalize Multiplicative.toAdd a b = x
    revert x
    decide
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  · rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, hxc⟩
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxc
    have ha : a = 1 := eq_one_of_sHom_entry (K := K) (m := m) fun b => by
      rw [← hc]
      simp
    rw [Subgroup.mem_bot, ha, map_one]
  · intro y
    obtain ⟨X, hX⟩ := y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two, Subgroup.coe_mul, ← hX, ← map_mul, OneMemClass.coe_one]
    have hXX : X * X = 1 := by
      apply Multiplicative.toAdd.injective
      ext i j
      simp only [toAdd_mul, toAdd_one, Matrix.add_apply, Matrix.zero_apply,
        CharTwo.add_self_eq_zero]
    rw [hXX, map_one]
  · intro hP
    have h1 : ψ (Multiplicative.ofAdd 1) ∈ ψ.range := ⟨_, rfl⟩
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hP h1)
    have : (scalar (BlockIdx m) c) (.inl (0, 0)) (.inl (0, 1)) =
        (fromBlocks (1 + yMat (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 1 :
          Matrix (BlockIdx m) (BlockIdx m) K) (.inl (0, 0)) (.inl (0, 1)) := by
      rw [hc]
      rfl
    simp [yMat, scalar_apply] at this
  · refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨a, rfl⟩ _ ⟨X, rfl⟩
    refine ⟨Multiplicative.ofAdd (threeCycleMat K ^ (a.toAdd 0).val * X.toAdd *
      threeCycleMat K ^ (-(a.toAdd 1)).val), ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    refine Subtype.ext ?_
    change fromBlocks (1 + yMat _) 0 0 1 * fromBlocks (sBlockMat a.toAdd) 0 0 1 =
      fromBlocks (sBlockMat a.toAdd) 0 0 1 * fromBlocks (1 + yMat X.toAdd) 0 0 1
    rw [fromBlocks_multiply, fromBlocks_multiply, mul_add, add_mul, sBlockMat_mul_yMat]
    simp

theorem four_le_localRank_PSL_of_eight_le [Finite K] {n : ℕ} (hn : 8 ≤ n) :
    4 ≤ localRank 3 (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hcard : Fintype.card (BlockIdx (n - 8)) = n := by
    simp only [BlockIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  rw [← localRank_eq_of_mulEquiv (pslReindex K (Fintype.equivFinOfCardEq hcard)) Nat.prime_three]
  exact four_le_localRank_PSL_blocks (n - 8)

end Blocks

end CFSG.RankThree.PartTwo.Census

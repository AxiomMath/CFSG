module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCRow4APt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C48Pf.FMod

namespace Stellmacher.PU.L3YC

@[expose] def blk4' (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![A 0 0, A 0 1, A 0 2, x 0;
     A 1 0, A 1 1, A 1 2, x 1;
     A 2 0, A 2 1, A 2 2, x 2;
     0, 0, 0, 1]

theorem det_blk4' (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2) :
    (blk4' A x).det = A.det := by
  rw [Matrix.det_succ_row (blk4' A x) (Fin.last 3), Fin.sum_univ_castSucc]
  have hsub : (blk4' A x).submatrix (Fin.last 3).succAbove Fin.castSucc = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h0 : ∀ j : Fin 3, (blk4' A x) (Fin.last 3) j.castSucc = 0 := fun j => by
    fin_cases j <;> simp [blk4']
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have h1 : (blk4' A x) (Fin.last 3) (Fin.last 3) = 1 := by simp [blk4']
  rw [h1]
  have : ((blk4' A x).submatrix (Fin.last 3).succAbove (Fin.last 3).succAbove) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [this]
  simp

@[expose] def hypStab : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) where
  carrier := {M | (Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ* (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
    Pi.single 3 1}
  one_mem' := by
    show (Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ*
      ((1 : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        Pi.single 3 1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  mul_mem' := by
    intro M N hM hN
    show (Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ*
      ((M * N : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        Pi.single 3 1
    have hM' : (Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ* (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      Pi.single 3 1 := hM
    have hN' : (Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ* (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      Pi.single 3 1 := hN
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.vecMul_vecMul, hM', hN']
  inv_mem' := by
    intro M hM
    have hM' : (Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ* (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      Pi.single 3 1 := hM
    show (Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ*
      ((M⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        Pi.single 3 1
    have h1 : ((Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ* (M : Matrix (Fin 4) (Fin 4) (ZMod 2))) ᵥ*
        ((M⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        (Pi.single 3 1 : Fin 4 → ZMod 2) := by
      rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
    rwa [hM'] at h1

theorem mem_hypStab_iff (M : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    M ∈ hypStab ↔ ∀ j : Fin 4, (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 j =
      if j = 3 then 1 else 0 := by
  constructor
  · intro h j
    have := congrFun h j
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply, eq_comm] using this
  · intro h
    show _ = _
    ext j
    simp [Matrix.vecMul, dotProduct, Pi.single_apply, h, eq_comm]

theorem exists_mat3_row : ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 →
    ∃ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det = 1 ∧ u ᵥ* A = v := by
  decide +kernel

theorem init_zero {w : Fin 4 → ZMod 2} (h : (fun i : Fin 3 => w i.castSucc) = 0) :
    w = 0 ∨ w = Pi.single 3 1 := by
  have h0 : w 0 = 0 := congrFun h 0
  have h1 : w 1 = 0 := congrFun h 1
  have h2 : w 2 = 0 := congrFun h 2
  have h3 : w 3 = 0 ∨ w 3 = 1 := by
    generalize w 3 = t
    revert t
    decide
  rcases h3 with e | e
  · left
    ext i
    fin_cases i <;> simp [*]
  · right
    ext i
    fin_cases i <;> simp [*]

@[expose] def blk4'SL (A : SpecialLinearGroup (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2) :
    SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨blk4' (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) x, by rw [det_blk4']; exact A.2⟩

theorem blk4'SL_coe (A : SpecialLinearGroup (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2) :
    ((blk4'SL A x : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      blk4' (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) x := rfl

theorem blk4'SL_mem (A : SpecialLinearGroup (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2) :
    blk4'SL A x ∈ hypStab := by
  rw [mem_hypStab_iff, blk4'SL_coe]
  intro j
  fin_cases j <;> simp [blk4']

theorem hypStab_trans (w w' : Fin 4 → ZMod 2) (hw0 : w ≠ 0) (hw1 : w ≠ Pi.single 3 1)
    (hw0' : w' ≠ 0) (hw1' : w' ≠ Pi.single 3 1) :
    ∃ b ∈ hypStab, w ᵥ* (b : Matrix (Fin 4) (Fin 4) (ZMod 2)) = w' := by
  have hwb : (fun i : Fin 3 => w i.castSucc) ≠ 0 := fun h => (init_zero h).elim hw0 hw1
  have hwb' : (fun i : Fin 3 => w' i.castSucc) ≠ 0 := fun h => (init_zero h).elim hw0' hw1'
  obtain ⟨A, hAdet, hA⟩ := exists_mat3_row _ _ hwb hwb'
  obtain ⟨x, hx⟩ := exists_dot _ hwb (w' 3 + w 3)
  let A' : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨A, hAdet⟩
  refine ⟨blk4'SL A' x, blk4'SL_mem _ _, ?_⟩
  have hx' : w 0 * x 0 + w 1 * x 1 + w 2 * x 2 = w' 3 + w 3 := by
    have := hx
    rw [dotProduct_comm] at this
    simpa [dotProduct, Fin.sum_univ_three] using this
  have hA0 := congrFun hA 0
  have hA1 := congrFun hA 1
  have hA2 := congrFun hA 2
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three] at hA0 hA1 hA2
  rw [blk4'SL_coe]
  ext j
  fin_cases j
  · simpa [blk4', A', Matrix.vecMul, dotProduct, Fin.sum_univ_four] using hA0
  · simpa [blk4', A', Matrix.vecMul, dotProduct, Fin.sum_univ_four] using hA1
  · simpa [blk4', A', Matrix.vecMul, dotProduct, Fin.sum_univ_four] using hA2
  · simp [blk4', A', Matrix.vecMul, dotProduct, Fin.sum_univ_four]
    have e : w 0 * x 0 + w 1 * x 1 + w 2 * x 2 + w 3 = w' 3 + w 3 + w 3 := by rw [hx']
    rw [e, add_assoc, Heis.zmod2_add_self, add_zero]

theorem sl_vecMul_mul {n : ℕ} (M N : SpecialLinearGroup (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    v ᵥ* ((M * N : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (v ᵥ* (M : Matrix (Fin n) (Fin n) (ZMod 2))) ᵥ* (N : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.vecMul_vecMul]

theorem sl_vecMul_self_inv {n : ℕ} (M : SpecialLinearGroup (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    (v ᵥ* (M : Matrix (Fin n) (Fin n) (ZMod 2))) ᵥ*
      ((M⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = v := by
  rw [← sl_vecMul_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

theorem hypStab_double (g h : SpecialLinearGroup (Fin 4) (ZMod 2)) (hg : g ∉ hypStab) :
    h ∈ hypStab ∨ ∃ a ∈ hypStab, ∃ b ∈ hypStab, h = a * g * b := by
  by_cases hh : h ∈ hypStab
  · exact Or.inl hh
  right
  have he0 : (Pi.single 3 1 : Fin 4 → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h 3
    simp at this
  have hne : ∀ M : SpecialLinearGroup (Fin 4) (ZMod 2), M ∉ hypStab →
      ((Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ* (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ 0 ∧
        (Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ* (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠
          Pi.single 3 1) := by
    intro M hM
    refine ⟨fun h0 => ?_, fun h1 => hM h1⟩
    have := sl_vecMul_self_inv M (Pi.single 3 1 : Fin 4 → ZMod 2)
    rw [h0, Matrix.zero_vecMul] at this
    exact he0 this.symm
  obtain ⟨h1, h2⟩ := hne g hg
  obtain ⟨h3, h4⟩ := hne h hh
  obtain ⟨b, hb, hbx⟩ := hypStab_trans _ _ h1 h2 h3 h4
  refine ⟨h * b⁻¹ * g⁻¹, ?_, b, hb, by group⟩
  show (Pi.single 3 1 : Fin 4 → ZMod 2) ᵥ*
    ((h * b⁻¹ * g⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      Pi.single 3 1
  rw [sl_vecMul_mul, sl_vecMul_mul, ← hbx, sl_vecMul_self_inv, sl_vecMul_self_inv]

theorem hypStab_shape (M : SpecialLinearGroup (Fin 4) (ZMod 2)) (hM : M ∈ hypStab) :
    (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      blk4' (Matrix.of fun i j : Fin 3 => (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.castSucc
        j.castSucc) (fun i : Fin 3 => (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.castSucc 3) := by
  have h := (mem_hypStab_iff M).1 hM
  have h0 : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 0 = 0 := by simpa using h 0
  have h1 : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 1 = 0 := by simpa using h 1
  have h2 : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 2 = 0 := by simpa using h 2
  have h3 : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 3 = 1 := by simpa using h 3
  ext i j
  fin_cases i <;> fin_cases j <;> first | rfl | simp [blk4', *]

theorem card_hypStab : Nat.card hypStab = 1344 := by
  have hdetA : ∀ M : hypStab, (Matrix.of fun i j : Fin 3 =>
      ((M : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.castSucc
        j.castSucc).det = 1 := by
    intro M
    have h1 := hypStab_shape M M.2
    have h2 := congrArg Matrix.det h1
    rw [det_blk4'] at h2
    rw [← h2]
    exact (M : SpecialLinearGroup (Fin 4) (ZMod 2)).2
  let e : hypStab ≃ SpecialLinearGroup (Fin 3) (ZMod 2) × (Fin 3 → ZMod 2) :=
    { toFun := fun M =>
        (⟨Matrix.of fun i j : Fin 3 => ((M : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) i.castSucc j.castSucc, hdetA M⟩,
         fun i => ((M : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) i.castSucc 3)
      invFun := fun p => ⟨blk4'SL p.1 p.2, blk4'SL_mem _ _⟩
      left_inv := fun M => by
        apply Subtype.ext
        apply Subtype.ext
        exact (hypStab_shape M M.2).symm
      right_inv := fun p => by
        refine Prod.ext ?_ ?_
        · apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j <;> simp [blk4'SL_coe, blk4']
        · funext i
          fin_cases i <;> simp [blk4'SL_coe, blk4'] }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
    Matrix.card_SL_field 3, ZMod.card]
  simp [Fin.prod_univ_succ]

end Stellmacher.PU.L3YC

end CFSG.Quasithin

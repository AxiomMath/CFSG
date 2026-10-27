module

public import CFSG.Quasithin.Background.C48PfFourModPfGrp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C48Pf.FMod

variable {n : ℕ}

theorem commute_single_iff {k l : Fin n} (v : Matrix (Fin n) (Fin n) (ZMod 2)) :
    v * (1 + Matrix.single k l 1) = (1 + Matrix.single k l 1) * v ↔
      (∀ i, i ≠ k → v i k = 0) ∧ (∀ j, j ≠ l → v l j = 0) ∧ v k k = v l l := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj]
  have key : ∀ i j, (v * Matrix.single k l (1 : ZMod 2)) i j = if j = l then v i k else 0 := by
    intro i j
    by_cases hj : j = l
    · subst hj
      simp [Matrix.mul_single_apply_same]
    · simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ hj, hj]
  have key' : ∀ i j, (Matrix.single k l (1 : ZMod 2) * v) i j = if i = k then v l j else 0 := by
    intro i j
    by_cases hi : i = k
    · subst hi
      simp [Matrix.single_mul_apply_same]
    · simp [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi, hi]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
    · have := congrFun (congrFun h i) l
      rw [key, key'] at this
      simpa [hi] using this
    · have := congrFun (congrFun h k) j
      rw [key, key'] at this
      simpa [hj] using this.symm
    · have := congrFun (congrFun h k) l
      rw [key, key'] at this
      simpa using this
  · rintro ⟨h1, h2, h3⟩
    ext i j
    rw [key, key']
    by_cases hj : j = l <;> by_cases hi : i = k
    · subst hj hi
      simp [h3]
    · subst hj
      simp [hi, h1 i hi]
    · subst hi
      simp [hj, h2 j hj]
    · simp [hi, hj]

@[expose] def CommCross (a m : ℕ) (v : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ (k l : Fin n), IsCross a m k l →
    v * (1 + Matrix.single k l 1) = (1 + Matrix.single k l 1) * v

theorem col_std {a m : ℕ} {v : Matrix (Fin n) (Fin n) (ZMod 2)} (hv : CommCross a m v)
    (hd : ∀ i, v i i = 1) (j : Fin n)
    (hj : ((j : ℕ) < a ∧ 1 ≤ m ∧ a < n) ∨ (a ≤ (j : ℕ) ∧ (j : ℕ) < a + m ∧ a + m < n)) :
    ∀ i, v i j = if i = j then 1 else 0 := by
  intro i
  by_cases hij : i = j
  · subst hij
    simp [hd]
  · rw [ite_eq_right_iff.2 fun h => absurd h hij]
    rcases hj with ⟨hja, hm, han⟩ | ⟨hja, hjm, han⟩
    · have hc : IsCross a m j ⟨a, han⟩ := Or.inl ⟨hja, le_rfl, by simp; omega⟩
      exact ((commute_single_iff v).1 (hv _ _ hc)).1 i hij
    · have hc : IsCross a m j ⟨a + m, han⟩ := Or.inr ⟨hja, hjm, le_rfl⟩
      exact ((commute_single_iff v).1 (hv _ _ hc)).1 i hij

theorem row_std {a m : ℕ} {v : Matrix (Fin n) (Fin n) (ZMod 2)} (hv : CommCross a m v)
    (hd : ∀ i, v i i = 1) (i : Fin n)
    (hi : (a ≤ (i : ℕ) ∧ (i : ℕ) < a + m ∧ 0 < a) ∨ (a + m ≤ (i : ℕ) ∧ 1 ≤ m)) :
    ∀ j, v i j = if i = j then 1 else 0 := by
  intro j
  by_cases hij : i = j
  · subst hij
    simp [hd]
  · rw [ite_eq_right_iff.2 fun h => absurd h hij]
    rcases hi with ⟨hia, him, ha⟩ | ⟨him, hm⟩
    · have hc : IsCross a m ⟨0, by omega⟩ i := Or.inl ⟨by simp; omega, hia, him⟩
      exact ((commute_single_iff v).1 (hv _ _ hc)).2.1 j (Ne.symm hij)
    · have hc : IsCross a m ⟨a, by omega⟩ i := Or.inr ⟨le_rfl, by simp; omega, him⟩
      exact ((commute_single_iff v).1 (hv _ _ hc)).2.1 j (Ne.symm hij)

@[expose] def Shape (c r : ℕ) (v : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  (∀ i j : Fin n, (j : ℕ) < c → v i j = if i = j then 1 else 0) ∧
    ∀ i j : Fin n, r ≤ (i : ℕ) → v i j = if i = j then 1 else 0

@[expose] def colC (v : Matrix (Fin n) (Fin n) (ZMod 2)) (j : Fin n) : Fin n → ZMod 2 :=
  (v - 1) *ᵥ Pi.single j 1

@[expose] def rowC (v : Matrix (Fin n) (Fin n) (ZMod 2)) (i : Fin n) : Fin n → ZMod 2 :=
  (v - 1)ᵀ *ᵥ Pi.single i 1

theorem colC_apply (v : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    colC v j i = v i j - if i = j then 1 else 0 := by
  simp [colC, Matrix.sub_apply, Matrix.one_apply]

theorem rowC_apply (v : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    rowC v i j = v i j - if i = j then 1 else 0 := by
  simp [rowC, Matrix.sub_apply, Matrix.one_apply, eq_comm]

theorem sub_one_mulVec_eq_zero {c r : ℕ} {v : Matrix (Fin n) (Fin n) (ZMod 2)} (hv : Shape c r v)
    {w : Fin n → ZMod 2} (hw : ∀ j : Fin n, c ≤ (j : ℕ) → w j = 0) : (v - 1) *ᵥ w = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : (j : ℕ) < c
  · rw [Matrix.sub_apply, hv.1 i j hj, Matrix.one_apply, sub_self, zero_mul]
  · rw [hw j (by omega), mul_zero]

theorem sub_one_transpose_mulVec_eq_zero {c r : ℕ} {v : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hv : Shape c r v) {w : Fin n → ZMod 2} (hw : ∀ j : Fin n, (j : ℕ) < r → w j = 0) :
    (v - 1)ᵀ *ᵥ w = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Matrix.transpose_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : r ≤ (j : ℕ)
  · rw [Matrix.sub_apply, hv.2 j i hj, Matrix.one_apply, sub_self, zero_mul]
  · rw [hw j (by omega), mul_zero]

theorem colC_eq_zero {c r : ℕ} {v : Matrix (Fin n) (Fin n) (ZMod 2)} (hv : Shape c r v)
    (j i : Fin n) (hi : r ≤ (i : ℕ)) : colC v j i = 0 := by
  rw [colC_apply, hv.2 i j hi, sub_self]

theorem rowC_eq_zero {c r : ℕ} {v : Matrix (Fin n) (Fin n) (ZMod 2)} (hv : Shape c r v)
    (i j : Fin n) (hj : (j : ℕ) < c) : rowC v i j = 0 := by
  rw [rowC_apply, hv.1 i j hj, sub_self]

theorem colC_mul {c : ℕ} {v w : Matrix (Fin n) (Fin n) (ZMod 2)} (hv : Shape c c v)
    (hw : Shape c c w) (j : Fin n) : colC (v * w) j = colC v j + colC w j := by
  have h1 : (v * w - 1) = (v - 1) * (w - 1) + (v - 1) + (w - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
    abel
  have h2 : (v - 1) *ᵥ colC w j = 0 :=
    sub_one_mulVec_eq_zero hv fun i hi => colC_eq_zero hw j i hi
  simp only [colC]
  rw [h1, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
  rw [show (w - 1) *ᵥ Pi.single j 1 = colC w j from rfl, h2, zero_add]

theorem rowC_mul {r : ℕ} {v w : Matrix (Fin n) (Fin n) (ZMod 2)} (hv : Shape r r v)
    (hw : Shape r r w) (i : Fin n) : rowC (v * w) i = rowC v i + rowC w i := by
  have h1 : (v * w - 1) = (v - 1) * (w - 1) + (v - 1) + (w - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
    abel
  have h2 : (w - 1)ᵀ *ᵥ rowC v i = 0 :=
    sub_one_transpose_mulVec_eq_zero hw fun j hj => rowC_eq_zero hv i j hj
  simp only [rowC]
  rw [h1, Matrix.transpose_add, Matrix.transpose_add, Matrix.add_mulVec, Matrix.add_mulVec,
    Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  rw [show (v - 1)ᵀ *ᵥ Pi.single i 1 = rowC v i from rfl, h2, zero_add]

theorem conj_sub_one (g : SpecialLinearGroup (Fin n) (ZMod 2))
    (v : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) * v * ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) - 1 =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * (v - 1) *
        ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have h : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]

theorem colC_conj {m : ℕ} (g : SpecialLinearGroup (Fin n) (ZMod 2))
    (hg : BlockForm 0 m ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)))
    {v : Matrix (Fin n) (Fin n) (ZMod 2)} (hv : Shape m m v) (j : Fin n) (hj : m ≤ (j : ℕ)) :
    colC ((g : Matrix (Fin n) (Fin n) (ZMod 2)) * v *
      ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) j =
        (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ colC v j := by
  set gi := ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
  have hw : ∀ i : Fin n, m ≤ (i : ℕ) →
      (gi *ᵥ Pi.single j 1 - Pi.single j 1 : Fin n → ZMod 2) i = 0 := by
    intro i hi
    rw [Pi.sub_apply, Matrix.mulVec_single_one, Matrix.col_apply, hg.2.2.2 i j (by omega)
      (by omega)]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have h0 := sub_one_mulVec_eq_zero hv hw
  have h1 : (v - 1) *ᵥ (gi *ᵥ Pi.single j 1) = (v - 1) *ᵥ Pi.single j 1 := by
    rw [Matrix.mulVec_sub, sub_eq_zero] at h0
    exact h0
  simp only [colC]
  rw [conj_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]

theorem rowC_conj {r : ℕ} (g : SpecialLinearGroup (Fin n) (ZMod 2))
    (hg : ∀ i j : Fin n, (i : ℕ) < r → (j : ℕ) < r →
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) i j = if i = j then 1 else 0)
    {v : Matrix (Fin n) (Fin n) (ZMod 2)} (hv : Shape r r v) (i : Fin n) (hi : (i : ℕ) < r) :
    rowC ((g : Matrix (Fin n) (Fin n) (ZMod 2)) * v *
      ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) i =
        ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ
          rowC v i := by
  set g' := (g : Matrix (Fin n) (Fin n) (ZMod 2))
  have hw : ∀ j : Fin n, (j : ℕ) < r →
      (g'ᵀ *ᵥ Pi.single i 1 - Pi.single i 1 : Fin n → ZMod 2) j = 0 := by
    intro j hj
    rw [Pi.sub_apply, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply,
      hg i j hi hj]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have h0 := sub_one_transpose_mulVec_eq_zero hv hw
  have h1 : (v - 1)ᵀ *ᵥ (g'ᵀ *ᵥ Pi.single i 1) = (v - 1)ᵀ *ᵥ Pi.single i 1 := by
    rw [Matrix.mulVec_sub, sub_eq_zero] at h0
    exact h0
  simp only [rowC]
  rw [conj_sub_one, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, h1]

theorem commute_of_middle {a m : ℕ} {g v : Matrix (Fin n) (Fin n) (ZMod 2)} (hg : BlockForm a m g)
    (hv : Shape (a + m) a v) : g * v = v * g := by
  have hN : ∀ i j : Fin n, (v - 1) i j ≠ 0 → (i : ℕ) < a ∧ a + m ≤ (j : ℕ) := by
    intro i j hij
    rw [Matrix.sub_apply, Matrix.one_apply] at hij
    refine ⟨?_, ?_⟩
    · by_contra hi
      exact hij (by rw [hv.2 i j (by omega), sub_self])
    · by_contra hj
      exact hij (by rw [hv.1 i j (by omega), sub_self])
  have h1 : g * (v - 1) = v - 1 := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · by_cases hi : (i : ℕ) < a
      · rw [hg.2.2.1 i i hi hi, ite_eq_left rfl, one_mul]
      · have : (v - 1) i j = 0 := by
          by_contra h
          exact hi (hN i j h).1
        rw [this, mul_zero]
    · intro k _ hki
      by_cases hk : (k : ℕ) < a
      · by_cases hi : (i : ℕ) < a
        · rw [hg.2.2.1 i k hi hk, ite_eq_right (Ne.symm hki), zero_mul]
        · rw [hg.1 i k (by omega) hk, zero_mul]
      · have : (v - 1) k j = 0 := by
          by_contra h
          exact hk (hN k j h).1
        rw [this, mul_zero]
    · simp
  have h2 : (v - 1) * g = v - 1 := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · by_cases hj : a + m ≤ (j : ℕ)
      · rw [hg.2.2.2 j j hj hj, ite_eq_left rfl, mul_one]
      · have : (v - 1) i j = 0 := by
          by_contra h
          exact hj (hN i j h).2
        rw [this, zero_mul]
    · intro k _ hkj
      by_cases hk : a + m ≤ (k : ℕ)
      · by_cases hj : a + m ≤ (j : ℕ)
        · rw [hg.2.2.2 k j hk hj, ite_eq_right hkj, mul_zero]
        · rw [hg.2.1 k j hk (by omega), mul_zero]
      · have : (v - 1) i k = 0 := by
          by_contra h
          exact hk (hN i k h).2
        rw [this, zero_mul]
    · simp
  have e1 : g * v = g + g * (v - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]; abel
  have e2 : v * g = g + (v - 1) * g := by rw [Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e1, e2, h1, h2]

end CFSG.Quasithin.C35Pf

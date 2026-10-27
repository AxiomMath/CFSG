module

public import CFSG.Quasithin.Vol2.Asc94.TSModel8

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

abbrev S2d (i j : Fin 5) : Prop := i.val + 2 ≤ j.val

theorem lt_S2d : ∀ i j, S2d i j → i < j := by decide

theorem trans_S2d : ∀ i k j, S2d i k → S2d k j → S2d i j := by decide

@[expose] def T2 : Subgroup Hc := patSubT S2d lt_S2d trans_S2d

theorem mem_T2 {x : Hc} : x ∈ T2 ↔ SuppIn S2d (cm x - 1) := Iff.rfl

theorem Tm_mul_super {x y : Hc} (hx : x ∈ Tm) (hy : y ∈ Tm) (i j : Fin 5)
    (hij : j.val = i.val + 1) : cm (x * y) i j = cm x i j + cm y i j := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  rw [cm_mul, Matrix.mul_apply, Finset.sum_eq_add i j hne]
  · rw [Tm_diag hx i, Tm_diag hy j, one_mul, mul_one, add_comm]
  · intro k _ hk
    by_cases hki : k < i
    · rw [Tm_entry_zero hx hki, zero_mul]
    · have hjk : j < k := by
        have h1 : i.val ≤ k.val := not_lt.1 hki
        have h2 : k.val ≠ i.val := fun h => hk.1 (Fin.ext h)
        have h3 : k.val ≠ j.val := fun h => hk.2 (Fin.ext h)
        show j.val < k.val
        omega
      rw [Tm_entry_zero hy hjk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem Tm_commutator_super {x y : Hc} (hx : x ∈ Tm) (hy : y ∈ Tm) (i j : Fin 5)
    (hij : j.val = i.val + 1) : cm (x * y * x⁻¹ * y⁻¹) i j = 0 := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hxi : x⁻¹ ∈ Tm := Tm.inv_mem hx
  have hyi : y⁻¹ ∈ Tm := Tm.inv_mem hy
  have hxy : x * y ∈ Tm := Tm.mul_mem hx hy
  have hxyx : x * y * x⁻¹ ∈ Tm := Tm.mul_mem hxy hxi
  have e1 := Tm_mul_super hxyx hyi i j hij
  have e2 := Tm_mul_super hxy hxi i j hij
  have e3 := Tm_mul_super hx hy i j hij
  have e4 := Tm_mul_super hx hxi i j hij
  have e5 := Tm_mul_super hy hyi i j hij
  rw [mul_inv_cancel, cm_one, Matrix.one_apply_ne hne] at e4 e5
  rw [e1, e2, e3]
  linear_combination -e4 - e5

theorem comm_Tm_le_T2 : ⁅Tm, Tm⁆ ≤ T2 := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  have hm : x * y * x⁻¹ * y⁻¹ ∈ Tm :=
    Tm.mul_mem (Tm.mul_mem (Tm.mul_mem hx hy) (Tm.inv_mem hx)) (Tm.inv_mem hy)
  rw [mem_T2]
  intro i j hij
  rw [Matrix.sub_apply]
  by_cases hji : j < i
  · rw [Tm_entry_zero hm hji, Matrix.one_apply_ne (ne_of_gt hji), sub_self]
  · by_cases hij' : i = j
    · subst hij'
      rw [Tm_diag hm i, Matrix.one_apply_eq, sub_self]
    · have hlt : i < j := lt_of_le_of_ne (not_lt.1 hji) hij'
      have hj : j.val = i.val + 1 := by
        have h1 : i.val < j.val := hlt
        have h2 : ¬ (i.val + 2 ≤ j.val) := hij
        omega
      rw [Tm_commutator_super hx hy i j hj, Matrix.one_apply_ne hij', sub_self]

theorem mul_S2d (N M : Mt) (hN : SuppIn S2d N) (hM : SuppIn S2d M) :
    N * M = Matrix.single 0 4 (N 0 2 * M 2 4) := by
  have n00 : N 0 0 = 0 := hN 0 0 (by decide)
  have n01 : N 0 1 = 0 := hN 0 1 (by decide)
  have n10 : N 1 0 = 0 := hN 1 0 (by decide)
  have n11 : N 1 1 = 0 := hN 1 1 (by decide)
  have n12 : N 1 2 = 0 := hN 1 2 (by decide)
  have n20 : N 2 0 = 0 := hN 2 0 (by decide)
  have n21 : N 2 1 = 0 := hN 2 1 (by decide)
  have n22 : N 2 2 = 0 := hN 2 2 (by decide)
  have n23 : N 2 3 = 0 := hN 2 3 (by decide)
  have n30 : N 3 0 = 0 := hN 3 0 (by decide)
  have n31 : N 3 1 = 0 := hN 3 1 (by decide)
  have n32 : N 3 2 = 0 := hN 3 2 (by decide)
  have n33 : N 3 3 = 0 := hN 3 3 (by decide)
  have n34 : N 3 4 = 0 := hN 3 4 (by decide)
  have n40 : N 4 0 = 0 := hN 4 0 (by decide)
  have n41 : N 4 1 = 0 := hN 4 1 (by decide)
  have n42 : N 4 2 = 0 := hN 4 2 (by decide)
  have n43 : N 4 3 = 0 := hN 4 3 (by decide)
  have n44 : N 4 4 = 0 := hN 4 4 (by decide)
  have m00 : M 0 0 = 0 := hM 0 0 (by decide)
  have m01 : M 0 1 = 0 := hM 0 1 (by decide)
  have m10 : M 1 0 = 0 := hM 1 0 (by decide)
  have m11 : M 1 1 = 0 := hM 1 1 (by decide)
  have m12 : M 1 2 = 0 := hM 1 2 (by decide)
  have m20 : M 2 0 = 0 := hM 2 0 (by decide)
  have m21 : M 2 1 = 0 := hM 2 1 (by decide)
  have m22 : M 2 2 = 0 := hM 2 2 (by decide)
  have m23 : M 2 3 = 0 := hM 2 3 (by decide)
  have m30 : M 3 0 = 0 := hM 3 0 (by decide)
  have m31 : M 3 1 = 0 := hM 3 1 (by decide)
  have m32 : M 3 2 = 0 := hM 3 2 (by decide)
  have m33 : M 3 3 = 0 := hM 3 3 (by decide)
  have m34 : M 3 4 = 0 := hM 3 4 (by decide)
  have m40 : M 4 0 = 0 := hM 4 0 (by decide)
  have m41 : M 4 1 = 0 := hM 4 1 (by decide)
  have m42 : M 4 2 = 0 := hM 4 2 (by decide)
  have m43 : M 4 3 = 0 := hM 4 3 (by decide)
  have m44 : M 4 4 = 0 := hM 4 4 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, n00, n01, n10, n11, n12, n20,
      n21, n22, n23, n30, n31, n32, n33, n34, n40, n41, n42, n43, n44, m00, m01, m10, m11, m12,
      m20, m21, m22, m23, m30, m31, m32, m33, m34, m40, m41, m42, m43, m44]

theorem single04_mul (c : ZMod 2) (w : Hc) :
    Matrix.single 0 4 c * cm w = Matrix.single 0 4 c := by
  ext a b
  by_cases ha : a = 0
  · subst ha
    rw [Matrix.single_mul_apply_same, cm_row4]
    by_cases hb : b = 4
    · subst hb
      simp [Matrix.single_apply]
    · simp [Matrix.single_apply, Matrix.one_apply, hb, Ne.symm hb]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha]
    simp [Matrix.single_apply, Ne.symm ha]

theorem commutator_T2 {x y : Hc} (hx : x ∈ T2) (hy : y ∈ T2) :
    ∃ c : ZMod 2, cm (x * y * x⁻¹ * y⁻¹) = 1 + Matrix.single 0 4 c := by
  have hN : SuppIn S2d (cm x - 1) := hx
  have hM : SuppIn S2d (cm y - 1) := hy
  have h1 := mul_S2d _ _ hN hM
  have h2 := mul_S2d _ _ hM hN
  obtain ⟨c, hxy⟩ : ∃ c : ZMod 2, cm x * cm y = cm y * cm x + Matrix.single 0 4 c := by
    refine ⟨(cm x - 1) 0 2 * (cm y - 1) 2 4 + (cm y - 1) 0 2 * (cm x - 1) 2 4, ?_⟩
    have e1 : cm x * cm y = 1 + (cm x - 1) + (cm y - 1) + (cm x - 1) * (cm y - 1) := by
      noncomm_ring
    have e2 : cm y * cm x = 1 + (cm y - 1) + (cm x - 1) + (cm y - 1) * (cm x - 1) := by
      noncomm_ring
    have hb := mat_add_self (Matrix.single (0 : Fin 5) (4 : Fin 5)
      ((cm y - 1) 0 2 * (cm x - 1) 2 4))
    rw [Matrix.single_add, e1, e2, h1, h2]
    calc (1 : Mt) + (cm x - 1) + (cm y - 1) + Matrix.single 0 4 ((cm x - 1) 0 2 * (cm y - 1) 2 4)
        = (1 + (cm y - 1) + (cm x - 1) + Matrix.single 0 4 ((cm x - 1) 0 2 * (cm y - 1) 2 4)) + 0 :=
          by abel
      _ = (1 + (cm y - 1) + (cm x - 1) + Matrix.single 0 4 ((cm x - 1) 0 2 * (cm y - 1) 2 4)) +
          (Matrix.single 0 4 ((cm y - 1) 0 2 * (cm x - 1) 2 4) +
            Matrix.single 0 4 ((cm y - 1) 0 2 * (cm x - 1) 2 4)) := by rw [hb]
      _ = _ := by abel
  refine ⟨c, ?_⟩
  rw [cm_mul, cm_mul, cm_mul, hxy]
  have hxx : cm x * cm x⁻¹ = 1 := cm_mul_inv x
  have hyy : cm y * cm y⁻¹ = 1 := cm_mul_inv y
  calc (cm y * cm x + Matrix.single 0 4 c) * cm x⁻¹ * cm y⁻¹
      = cm y * (cm x * cm x⁻¹) * cm y⁻¹ + Matrix.single 0 4 c * cm x⁻¹ * cm y⁻¹ := by
        noncomm_ring
    _ = 1 + Matrix.single 0 4 c := by
        rw [hxx, mul_one, hyy, single04_mul, single04_mul]

theorem comm_T2_le_Z : ⁅T2, T2⁆ ≤ Subgroup.zpowers zt := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  obtain ⟨c, hc⟩ := commutator_T2 hx hy
  rcases eq_one_or_zt _ c hc with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers _

theorem comm2_Tm_le_Z : ⁅⁅Tm, Tm⁆, ⁅Tm, Tm⁆⁆ ≤ Subgroup.zpowers zt :=
  (Subgroup.commutator_mono comm_Tm_le_T2 comm_Tm_le_T2).trans comm_T2_le_Z

end CFSG.Quasithin.A94.L52

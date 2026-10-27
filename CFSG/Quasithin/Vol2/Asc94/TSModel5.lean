module

public import CFSG.Quasithin.Vol2.Asc94.TSModel1

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

@[expose] def NH1 : Subgroup Hc where
  carrier := {x | cm x 2 1 = 0 ∧ cm x 3 1 = 0}
  mul_mem' := fun {x y} hx hy => by
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, ?_⟩ <;>
    · simp only [cm_mul, Matrix.mul_apply, Fin.sum_univ_five, cm_col0, cm_row4, hx1, hx2, hy1, hy2]
      simp [Matrix.one_apply]
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp [cm_one, Matrix.one_apply]
  inv_mem' := fun {x} hx => by
    classical
    have hpow : ∀ n : ℕ, cm (x ^ n) 2 1 = 0 ∧ cm (x ^ n) 3 1 = 0 := by
      intro n
      induction n with
      | zero => refine ⟨?_, ?_⟩ <;> simp [cm_one, Matrix.one_apply]
      | succ n ih =>
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨hn1, hn2⟩ := ih
        rw [pow_succ]
        refine ⟨?_, ?_⟩ <;>
        · simp only [cm_mul, Matrix.mul_apply, Fin.sum_univ_five, cm_col0, cm_row4, hx1, hx2, hn1,
            hn2]
          simp [Matrix.one_apply]
    have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [hinv]
    exact hpow _

theorem mem_A1 {x : Hc} : x ∈ A1 ↔ SuppIn SA (cm x - 1) := Iff.rfl

theorem lowleft_NH1 {y : Hc} (hy : y ∈ NH1) {i l : Fin 5} (hi : 2 ≤ i.val) (hl : l.val ≤ 1) :
    cm y i l = 0 := by
  obtain ⟨h1, h2⟩ := hy
  have hl' : l = 0 ∨ l = 1 := by
    revert hl
    revert l
    decide
  have hi' : i = 2 ∨ i = 3 ∨ i = 4 := by
    revert hi
    revert i
    decide
  rcases hl' with rfl | rfl
  · rw [cm_col0]
    rcases hi' with rfl | rfl | rfl <;> simp [Matrix.one_apply]
  · rcases hi' with rfl | rfl | rfl
    · exact h1
    · exact h2
    · rw [cm_row4]
      simp [Matrix.one_apply]

theorem conj_NH1_A1 {y a : Hc} (hy : y ∈ NH1) (ha : a ∈ A1) : y * a * y⁻¹ ∈ A1 := by
  have hyi : y⁻¹ ∈ NH1 := NH1.inv_mem hy
  rw [mem_A1] at ha ⊢
  have e : cm (y * a * y⁻¹) - 1 = cm y * (cm a - 1) * cm y⁻¹ := by
    have h1 : cm y * cm y⁻¹ = 1 := cm_mul_inv y
    have h2 : cm y * (cm a - 1) * cm y⁻¹ = cm y * cm a * cm y⁻¹ - cm y * cm y⁻¹ := by
      noncomm_ring
    rw [h2, h1, cm_mul, cm_mul]
  intro i j hij
  rw [e, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hlm : SA l m
  · have hij' : 2 ≤ i.val ∨ j.val ≤ 1 := by
      by_contra hcon
      push Not at hcon
      exact hij ⟨by omega, by omega⟩
    rcases hij' with hi | hj
    · rw [lowleft_NH1 hy hi hlm.1]
      simp
    · rw [lowleft_NH1 hyi hlm.2 hj]
      simp
  · rw [ha l m hlm]
    simp

theorem normalizer_A1_eq : Subgroup.normalizer (A1 : Set Hc) = NH1 := by
  apply le_antisymm
  · intro x hx
    have hxi := Subgroup.inv_mem _ hx
    have key : ∀ j : Fin 5, 2 ≤ j.val → cm x j 1 = 0 := by
      intro j hj
      have hjn : (0 : Fin 5) < j := by
        have : 0 < j.val := by omega
        exact this
      have hmem : unipS 0 j hjn 1 ∈ A1 := unipS_mem_patSub hSA _ 1 ⟨by simp, hj⟩
      have h1 : x⁻¹ * unipS 0 j hjn 1 * x⁻¹⁻¹ ∈ A1 := by
        have := (Subgroup.mem_normalizer_iff.1 hxi (unipS 0 j hjn 1)).1 hmem
        exact this
      rw [mem_A1] at h1
      have h2 := h1 0 1 (by simp)
      have e : cm (x⁻¹ * unipS 0 j hjn 1 * x⁻¹⁻¹) - 1 = cm x⁻¹ * Matrix.single 0 j 1 * cm x := by
        have hh : cm x⁻¹ * cm x = 1 := cm_inv_mul x
        rw [inv_inv, cm_mul, cm_mul, cm_unipS]
        calc cm x⁻¹ * (1 + Matrix.single 0 j 1) * cm x - 1
            = cm x⁻¹ * cm x - 1 + cm x⁻¹ * Matrix.single 0 j 1 * cm x := by noncomm_ring
          _ = cm x⁻¹ * Matrix.single 0 j 1 * cm x := by rw [hh]; abel
      rw [e] at h2
      have h3 : (cm x⁻¹ * (Matrix.single 0 j 1 : Mt) * cm x) 0 1 = cm x⁻¹ 0 0 * cm x j 1 := by
        simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_five]
      rw [h3, cm_00] at h2
      simpa using h2
    exact ⟨key 2 (by decide), key 3 (by decide)⟩
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact conj_NH1_A1 hx ha
    · intro ha
      have hxi : x⁻¹ ∈ NH1 := NH1.inv_mem hx
      have h := conj_NH1_A1 hxi ha
      have e : x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a := by group
      rwa [e] at h

end CFSG.Quasithin.A94.L52

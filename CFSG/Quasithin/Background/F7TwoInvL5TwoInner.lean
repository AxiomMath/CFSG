module

public import CFSG.Quasithin.Background.F7TwoInvSeed
public import CFSG.Quasithin.Background.F7TwoInvL5TwoElem
public import CFSG.GroupTheory.GL52.InvolutionsConj

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GroupTheory.GL52

@[expose] def xt : Set G52 :=
  {swp 0 4} ∪ {g | ∃ (i j : Fin 5) (h : i ≠ j),
    (i < j ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 1) ∨ (i = 3 ∧ j = 2)) ∧ g = elem i j h}

theorem closure_xt : Subgroup.closure xt = ⊤ := by
  set S := Subgroup.closure xt with hS
  have hw : swp 0 4 ∈ S := Subgroup.subset_closure (Or.inl rfl)
  have hd : ∀ (i j : Fin 5) (h : i ≠ j),
      (i < j ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 1) ∨ (i = 3 ∧ j = 2)) → elem i j h ∈ S :=
    fun i j h hc => Subgroup.subset_closure (Or.inr ⟨i, j, h, hc, rfl⟩)
  refine eq_top_of_elem_mem fun i j h => ?_
  fin_cases i <;> fin_cases j <;>
    first | exact absurd rfl h | exact hd _ _ _ (by decide) | skip
  · exact elem_mem_of_conj hw (i' := 1) (j' := 4) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide))
  · exact elem_mem_of_conj hw (i' := 2) (j' := 4) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide))
  · exact elem_mem_of_conj hw (i' := 3) (j' := 4) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide))
  · exact elem_mem_of_conj hw (i' := 0) (j' := 4) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide))
  · exact elem_mem_of_conj hw (i' := 0) (j' := 1) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide))
  · exact elem_mem_of_conj hw (i' := 0) (j' := 2) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide))
  · exact elem_mem_of_conj hw (i' := 0) (j' := 3) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide))

theorem invT0_comm_elem : ∀ (i j : Fin 5) (h : i ≠ j),
    (i < j ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 1) ∨ (i = 3 ∧ j = 2)) →
      invT0 * elem i j h = elem i j h * invT0 := by decide +kernel

theorem swp_mem_invXi_t0 : swp 0 4 ∈ invXiAut (MulAut.conj invT0) := by
  rw [mem_invXiAut_iff]
  refine pow_two_pow_ne_one_of_pow (s := 0) (m := 3) (by decide) ?_ ?_
  · simp only [MulAut.conj_apply]
    exact Units.ext (by decide +kernel)
  · simp only [MulAut.conj_apply]
    intro h
    have := congrArg (fun g : G52 => (g : CFSG.GroupTheory.GL52.M5)) h
    revert this
    decide +kernel

theorem invAutGen_conj_invT0 : InvAutGen G52 (MulAut.conj invT0) := by
  refine invAutGen_of_seeds closure_xt ?_ ⟨swp 0 4, Or.inl rfl, swp_mem_invXi_t0⟩
  rintro x (rfl | ⟨i, j, h, hc, rfl⟩)
  · exact Or.inl swp_mem_invXi_t0
  · right
    have := invT0_comm_elem i j h hc
    simp only [MulAut.conj_apply]
    rw [this]
    group

@[expose] def xu : Set G52 :=
  {swp 0 3, swp 1 4} ∪ {g | ∃ (i j : Fin 5) (h : i ≠ j), i ≤ 2 ∧ 2 ≤ j ∧ g = elem i j h}

theorem closure_xu : Subgroup.closure xu = ⊤ := by
  set S := Subgroup.closure xu with hS
  have hw₁ : swp 0 3 ∈ S := Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have hw₂ : swp 1 4 ∈ S := Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hw₁₂ : swp 0 3 * swp 1 4 ∈ S := S.mul_mem hw₁ hw₂
  have hd : ∀ (i j : Fin 5) (h : i ≠ j), i ≤ 2 → 2 ≤ j → elem i j h ∈ S :=
    fun i j h hi hj => Subgroup.subset_closure (Or.inr ⟨i, j, h, hi, hj, rfl⟩)
  refine eq_top_of_elem_mem fun i j h => ?_
  fin_cases i <;> fin_cases j <;>
    first | exact absurd rfl h | exact hd _ _ _ (by decide) (by decide) | skip
  · exact elem_mem_of_conj hw₂ (i' := 0) (j' := 4) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₁ (i' := 1) (j' := 3) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₁ (i' := 2) (j' := 3) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₂ (i' := 2) (j' := 4) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₁ (i' := 0) (j' := 3) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₁₂ (i' := 0) (j' := 4) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₁ (i' := 0) (j' := 2) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₁ (i' := 0) (j' := 4) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₁₂ (i' := 1) (j' := 3) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₂ (i' := 1) (j' := 4) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₂ (i' := 1) (j' := 2) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))
  · exact elem_mem_of_conj hw₂ (i' := 1) (j' := 3) (h' := by decide) (by decide +kernel)
      (hd _ _ _ (by decide) (by decide))

theorem invU0_comm_elem : ∀ (i j : Fin 5) (h : i ≠ j), i ≤ 2 → 2 ≤ j →
    invU0 * elem i j h = elem i j h * invU0 := by decide +kernel

theorem swp_mem_invXi_u0 {a b : Fin 5} (hab : (a, b) = (0, 3) ∨ (a, b) = (1, 4)) :
    swp a b ∈ invXiAut (MulAut.conj invU0) := by
  rw [mem_invXiAut_iff]
  refine pow_two_pow_ne_one_of_pow (s := 0) (m := 3) (by decide) ?_ ?_
  · simp only [MulAut.conj_apply]
    rcases hab with h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;>
      exact Units.ext (by decide +kernel)
  · simp only [MulAut.conj_apply]
    intro h
    have := congrArg (fun g : G52 => (g : CFSG.GroupTheory.GL52.M5)) h
    rcases hab with h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;>
      · revert this
        decide +kernel

theorem invAutGen_conj_invU0 : InvAutGen G52 (MulAut.conj invU0) := by
  refine invAutGen_of_seeds closure_xu ?_ ⟨swp 0 3, Or.inl (Or.inl rfl),
    swp_mem_invXi_u0 (Or.inl rfl)⟩
  rintro x ((rfl | rfl) | ⟨i, j, h, hi, hj, rfl⟩)
  · exact Or.inl (swp_mem_invXi_u0 (Or.inl rfl))
  · exact Or.inl (swp_mem_invXi_u0 (Or.inr rfl))
  · right
    have := invU0_comm_elem i j h hi hj
    simp only [MulAut.conj_apply]
    rw [this]
    group

theorem invAutGen_conj_of_involution {A : G52} (hA : A * A = 1) (hA1 : A ≠ 1) :
    InvAutGen G52 (MulAut.conj A) := by
  have hsq : A ^ 2 = 1 := by rw [pow_two]; exact hA
  rcases inv_commDim_eq_one_or_two hsq hA1 with h1 | h2
  · obtain ⟨c, hc⟩ := isConj_iff.1 (inv_isConj_t0 hsq h1)
    exact invAutGen_conj_of_conj c hc.symm invAutGen_conj_invT0
  · obtain ⟨c, hc⟩ := isConj_iff.1 (inv_isConj_u0 hsq h2)
    exact invAutGen_conj_of_conj c hc.symm invAutGen_conj_invU0

end CFSG.Quasithin.F7Two

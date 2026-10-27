module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.Native

open CFSG.Blueprint

theorem exists_real_three_of_involution_product {G : Type*} [Group G] {t w : G}
    (ht : t ^ 2 = 1) (h6 : (t * (w * t * w⁻¹)) ^ 6 = 1) (h2 : (t * (w * t * w⁻¹)) ^ 2 ≠ 1)
    (h3 : (t * (w * t * w⁻¹)) ^ 3 ≠ 1) :
    ∃ x z b : G, orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ := by
  set s := w * t * w⁻¹ with hs
  set y := t * s with hy
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ht])
  have hs2 : s * s = 1 := by
    rw [hs, show w * t * w⁻¹ * (w * t * w⁻¹) = w * (t * t) * w⁻¹ by group, ← pow_two, ht,
      mul_one, mul_inv_cancel]
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hconj : t * y * t⁻¹ = y⁻¹ := by
    rw [hy, mul_inv_rev, hs', ht', ← mul_assoc, ← pow_two, ht, one_mul]
  refine ⟨y ^ 2, y ^ 3, t, orderOf_eq_prime ?_ h2, orderOf_eq_prime ?_ h3,
    (Commute.pow_pow_self y 2 3).eq, ?_⟩
  · rw [← pow_mul]
    exact h6
  · rw [← pow_mul]
    exact h6
  · rw [← conj_pow, hconj, inv_pow]

theorem exists_real_three_of_mulEquiv {S G : Type*} [Group S] [Group G] (e : S ≃* G)
    (h : ∃ x z b : G, orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹) :
    ∃ x z b : S, orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ := by
  obtain ⟨x, z, b, hx, hz, hxz, hb⟩ := h
  refine ⟨e.symm x, e.symm z, e.symm b, by rw [MulEquiv.orderOf_eq, hx],
    by rw [MulEquiv.orderOf_eq, hz], ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hxz]
  · rw [← map_inv, ← map_mul, ← map_mul, hb, map_inv]

abbrev m11T : NativeSporadic.M11 :=
  ⟨List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m11W : NativeSporadic.M11 :=
  ⟨List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

abbrev m12T : NativeSporadic.M12 :=
  ⟨List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m12W : NativeSporadic.M12 :=
  ⟨List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
      List.formPerm [5, 9, 6],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

abbrev m22T : NativeSporadic.M22 :=
  ⟨List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
      List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] *
      List.formPerm [10, 13],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m22W : NativeSporadic.M22 :=
  ⟨List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
      List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

abbrev m23T : NativeSporadic.M23 :=
  ⟨List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
      List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
      List.formPerm [20, 21],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m23W : NativeSporadic.M23 :=
  ⟨List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
      List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

abbrev m24T : NativeSporadic.M24 :=
  ⟨List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
      List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] *
      List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] *
      List.formPerm [19, 23] * List.formPerm [21, 22],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m24B : NativeSporadic.M24 :=
  ⟨List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
      List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

abbrev m24W : NativeSporadic.M24 := m24B * m24T * m24B⁻¹

theorem m11_witness :
    ∃ x z b : NativeSporadic.M11,
      orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ :=
  exists_real_three_of_involution_product (t := m11T) (w := m11W)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem m12_witness :
    ∃ x z b : NativeSporadic.M12,
      orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ :=
  exists_real_three_of_involution_product (t := m12T) (w := m12W)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem m22_witness :
    ∃ x z b : NativeSporadic.M22,
      orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ :=
  exists_real_three_of_involution_product (t := m22T) (w := m22W)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem m23_witness :
    ∃ x z b : NativeSporadic.M23,
      orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ :=
  exists_real_three_of_involution_product (t := m23T) (w := m23W)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem m24_witness :
    ∃ x z b : NativeSporadic.M24,
      orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ :=
  exists_real_three_of_involution_product (t := m24T) (w := m24W)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem five_mathieu_real_three_elements_centralizing_involutions {S : Type*} [Group S]
    (hS : Nonempty (S ≃* NativeSporadic.M11) ∨ Nonempty (S ≃* NativeSporadic.M12) ∨
      Nonempty (S ≃* NativeSporadic.M22) ∨ Nonempty (S ≃* NativeSporadic.M23) ∨
      Nonempty (S ≃* NativeSporadic.M24)) :
    ∃ x z b : S, orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ := by
  rcases hS with h | h | h | h | h <;> obtain ⟨e⟩ := h
  · exact exists_real_three_of_mulEquiv e m11_witness
  · exact exists_real_three_of_mulEquiv e m12_witness
  · exact exists_real_three_of_mulEquiv e m22_witness
  · exact exists_real_three_of_mulEquiv e m23_witness
  · exact exists_real_three_of_mulEquiv e m24_witness

end CFSG.RankThree.Native

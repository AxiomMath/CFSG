module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenPerm
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.OddStandard.AltStdSec CFSG.LocalAnalysis.ComponentInitial Equiv Subgroup

@[expose] def s16c11_v1_T : Finset (Fin 10) := Finset.univ.erase 0

theorem s16c11_v1_mem_T {i : Fin 10} : i ∈ s16c11_v1_T ↔ i ≠ 0 := by
  simp [s16c11_v1_T]

@[expose] noncomputable def s16c11_v1_eT : Fin 9 ≃ ↥(s16c11_v1_T) where
  toFun i := ⟨i.succ, s16c11_v1_mem_T.2 (Fin.succ_ne_zero i)⟩
  invFun x := x.1.pred (s16c11_v1_mem_T.1 x.2)
  left_inv i := by
    apply Fin.ext
    simp
  right_inv x := Subtype.ext (Fin.succ_pred x.1 (s16c11_v1_mem_T.1 x.2))

theorem s16c11_v1_eT_zero : s16c11_v1_eT 0 = ⟨1, s16c11_v1_mem_T.2 (by decide)⟩ := rfl

theorem s16c11_v1_eT_one : s16c11_v1_eT 1 = ⟨2, s16c11_v1_mem_T.2 (by decide)⟩ := rfl

@[expose] def s16c11_v1_c123 : ↥(alternatingGroup (Fin 10)) :=
  ⟨swap 1 2 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def s16c11_v1_c345 : ↥(alternatingGroup (Fin 10)) :=
  ⟨swap 3 4 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def s16c11_v1_c567 : ↥(alternatingGroup (Fin 10)) :=
  ⟨swap 5 6 * swap 6 7, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def s16c11_v1_c789 : ↥(alternatingGroup (Fin 10)) :=
  ⟨swap 7 8 * swap 8 9, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def s16c11_v1_H : Subgroup ↥(alternatingGroup (Fin 10)) :=
  Subgroup.closure
    ({s16c11_v1_c123, s16c11_v1_c345, s16c11_v1_c567, s16c11_v1_c789} : Set _)

theorem s16c11_v1_c123_mem : s16c11_v1_c123 ∈ s16c11_v1_H :=
  Subgroup.subset_closure (by simp [s16c11_v1_H])

theorem s16c11_v1_c345_mem : s16c11_v1_c345 ∈ s16c11_v1_H :=
  Subgroup.subset_closure (by simp [s16c11_v1_H])

theorem s16c11_v1_c567_mem : s16c11_v1_c567 ∈ s16c11_v1_H :=
  Subgroup.subset_closure (by simp [s16c11_v1_H])

theorem s16c11_v1_c789_mem : s16c11_v1_c789 ∈ s16c11_v1_H :=
  Subgroup.subset_closure (by simp [s16c11_v1_H])

@[expose] def s16c11_v1_Q : Subgroup (Perm (Fin 10)) :=
  s16c11_v1_H.map (alternatingGroup (Fin 10)).subtype

theorem s16c11_v1_star_mem (k : Fin 10) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    swap 1 k * swap 1 2 ∈ s16c11_v1_Q := by
  have h5 : s16c11_v1_c345⁻¹ * s16c11_v1_c123 * s16c11_v1_c345 ∈ s16c11_v1_H :=
    s16c11_v1_H.mul_mem (s16c11_v1_H.mul_mem (s16c11_v1_H.inv_mem s16c11_v1_c345_mem)
      s16c11_v1_c123_mem) s16c11_v1_c345_mem
  have h7 : s16c11_v1_c567⁻¹ * (s16c11_v1_c345⁻¹ * s16c11_v1_c123 * s16c11_v1_c345) *
      s16c11_v1_c567 ∈ s16c11_v1_H :=
    s16c11_v1_H.mul_mem (s16c11_v1_H.mul_mem (s16c11_v1_H.inv_mem s16c11_v1_c567_mem) h5)
      s16c11_v1_c567_mem
  have h9 : s16c11_v1_c789⁻¹ * (s16c11_v1_c567⁻¹ * (s16c11_v1_c345⁻¹ * s16c11_v1_c123 *
      s16c11_v1_c345) * s16c11_v1_c567) * s16c11_v1_c789 ∈ s16c11_v1_H :=
    s16c11_v1_H.mul_mem (s16c11_v1_H.mul_mem (s16c11_v1_H.inv_mem s16c11_v1_c789_mem) h7)
      s16c11_v1_c789_mem
  have h4 : s16c11_v1_c345 * s16c11_v1_c123 * s16c11_v1_c345⁻¹ ∈ s16c11_v1_H :=
    s16c11_v1_H.mul_mem (s16c11_v1_H.mul_mem s16c11_v1_c345_mem s16c11_v1_c123_mem)
      (s16c11_v1_H.inv_mem s16c11_v1_c345_mem)
  have h6 : s16c11_v1_c567 * (s16c11_v1_c345⁻¹ * s16c11_v1_c123 * s16c11_v1_c345) *
      s16c11_v1_c567⁻¹ ∈ s16c11_v1_H :=
    s16c11_v1_H.mul_mem (s16c11_v1_H.mul_mem s16c11_v1_c567_mem h5)
      (s16c11_v1_H.inv_mem s16c11_v1_c567_mem)
  have h8 : s16c11_v1_c789 * (s16c11_v1_c567⁻¹ * (s16c11_v1_c345⁻¹ * s16c11_v1_c123 *
      s16c11_v1_c345) * s16c11_v1_c567) * s16c11_v1_c789⁻¹ ∈ s16c11_v1_H :=
    s16c11_v1_H.mul_mem (s16c11_v1_H.mul_mem s16c11_v1_c789_mem h7)
      (s16c11_v1_H.inv_mem s16c11_v1_c789_mem)
  have key : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 →
      ∃ h ∈ s16c11_v1_H, (h : Perm (Fin 10)) = swap 1 k * swap 1 2 := by
    intro k hk0 hk1
    fin_cases k
    · exact absurd rfl hk0
    · exact absurd rfl hk1
    · exact ⟨1, s16c11_v1_H.one_mem, by decide⟩
    · exact ⟨s16c11_v1_c123, s16c11_v1_c123_mem, by decide⟩
    · exact ⟨s16c11_v1_c345 * s16c11_v1_c123 * s16c11_v1_c345⁻¹, h4, by decide⟩
    · exact ⟨s16c11_v1_c345⁻¹ * s16c11_v1_c123 * s16c11_v1_c345, h5, by decide⟩
    · exact ⟨s16c11_v1_c567 * (s16c11_v1_c345⁻¹ * s16c11_v1_c123 * s16c11_v1_c345) *
        s16c11_v1_c567⁻¹, h6, by decide⟩
    · exact ⟨s16c11_v1_c567⁻¹ * (s16c11_v1_c345⁻¹ * s16c11_v1_c123 * s16c11_v1_c345) *
        s16c11_v1_c567, h7, by decide⟩
    · exact ⟨s16c11_v1_c789 * (s16c11_v1_c567⁻¹ * (s16c11_v1_c345⁻¹ * s16c11_v1_c123 *
        s16c11_v1_c345) * s16c11_v1_c567) * s16c11_v1_c789⁻¹, h8, by decide⟩
    · exact ⟨s16c11_v1_c789⁻¹ * (s16c11_v1_c567⁻¹ * (s16c11_v1_c345⁻¹ * s16c11_v1_c123 *
        s16c11_v1_c345) * s16c11_v1_c567) * s16c11_v1_c789, h9, by decide⟩
  obtain ⟨h, hh, hhe⟩ := key k hk0 hk1
  exact Subgroup.mem_map.2 ⟨h, hh, hhe⟩

private theorem s16c11_v1_permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (x y : α) :
    e.permCongr (swap x y) = swap (e x) (e y) := by
  ext z
  rw [Equiv.permCongr_apply]
  by_cases hx : z = e x
  · rw [hx, Equiv.symm_apply_apply, swap_apply_left, swap_apply_left]
  · by_cases hy : z = e y
    · rw [hy, Equiv.symm_apply_apply, swap_apply_right, swap_apply_right]
    · have hzx : e.symm z ≠ x := fun h => hx (by rw [← h, Equiv.apply_symm_apply])
      have hzy : e.symm z ≠ y := fun h => hy (by rw [← h, Equiv.apply_symm_apply])
      rw [swap_apply_of_ne_of_ne hzx hzy, swap_apply_of_ne_of_ne hx hy,
        Equiv.apply_symm_apply]

theorem s16c11_v1_altSub_le_Q : altSub s16c11_v1_T ≤ s16c11_v1_Q := by
  let φ : Perm (Fin 9) →* Perm (Fin 10) :=
    (Perm.ofSubtype (p := fun x : Fin 10 => x ∈ s16c11_v1_T)).comp
      (Equiv.permCongrHom s16c11_v1_eT).toMonoidHom
  have hφswap : ∀ a b : Fin 9, φ (swap a b) =
      swap (s16c11_v1_eT a : Fin 10) (s16c11_v1_eT b : Fin 10) := by
    intro a b
    show Perm.ofSubtype (Equiv.permCongr s16c11_v1_eT (swap a b)) = _
    rw [s16c11_v1_permCongr_swap, Perm.ofSubtype_swap_eq]
  have he0 : (s16c11_v1_eT 0 : Fin 10) = 1 := congrArg Subtype.val s16c11_v1_eT_zero
  have he1 : (s16c11_v1_eT 1 : Fin 10) = 2 := congrArg Subtype.val s16c11_v1_eT_one
  have hstar : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 →
      swap 0 j * swap 0 1 ∈ s16c11_v1_Q.comap φ := by
    intro j hj0 hj1
    show φ (swap 0 j * swap 0 1) ∈ s16c11_v1_Q
    rw [map_mul, hφswap, hφswap, he0, he1]
    refine s16c11_v1_star_mem (s16c11_v1_eT j)
      (s16c11_v1_mem_T.1 (s16c11_v1_eT j).2) ?_
    intro h
    exact hj0 (s16c11_v1_eT.injective (Subtype.ext (h.trans he0.symm)))
  have hall : ∀ u v w : Fin 9, u ≠ v → u ≠ w → v ≠ w →
      swap (s16c11_v1_eT u : Fin 10) (s16c11_v1_eT v : Fin 10) *
        swap (s16c11_v1_eT u : Fin 10) (s16c11_v1_eT w : Fin 10) ∈ s16c11_v1_Q := by
    intro u v w huv huw hvw
    have h := swap_mul_swap_mem_of_forall (s16c11_v1_Q.comap φ) hstar huv huw hvw
    change φ (swap u v * swap u w) ∈ s16c11_v1_Q at h
    rw [map_mul, hφswap, hφswap] at h
    exact h
  refine altSub_le_of_cyc3 fun x y z hx hy hz hxy hyz hxz => ?_
  obtain ⟨u, hu⟩ := s16c11_v1_eT.surjective ⟨x, hx⟩
  obtain ⟨v, hv⟩ := s16c11_v1_eT.surjective ⟨y, hy⟩
  obtain ⟨w, hw⟩ := s16c11_v1_eT.surjective ⟨z, hz⟩
  have huv : u ≠ v := fun h => hxy (by
    have h' : s16c11_v1_eT u = s16c11_v1_eT v := by rw [h]
    rw [hu, hv] at h'
    exact congrArg Subtype.val h')
  have huw : u ≠ w := fun h => hxz (by
    have h' : s16c11_v1_eT u = s16c11_v1_eT w := by rw [h]
    rw [hu, hw] at h'
    exact congrArg Subtype.val h')
  have hvw : v ≠ w := fun h => hyz (by
    have h' : s16c11_v1_eT v = s16c11_v1_eT w := by rw [h]
    rw [hv, hw] at h'
    exact congrArg Subtype.val h')
  have h := hall u w v huw huv hvw.symm
  rw [show (s16c11_v1_eT u : Fin 10) = x from congrArg Subtype.val hu,
    show (s16c11_v1_eT w : Fin 10) = z from congrArg Subtype.val hw,
    show (s16c11_v1_eT v : Fin 10) = y from congrArg Subtype.val hv] at h
  have hcyc : cyc3 x y z = swap x z * swap x y := by
    rw [cyc3]
    conv_lhs => rw [swap_comm x y]
    exact swap_mul_swap_rotate (Ne.symm hxy) hyz hxz
  rwa [hcyc]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.CGT.PushingUpLit.SolK.GenFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

section Tame

variable {J : Type*} [Group J]

theorem false_of_abelian_index_le_two {α β ω : J} (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hne : α ≠ β)
    (hβ : β ^ 2 = 1) (hαβ : α * β = β * α) (hω : ω * α * ω⁻¹ = β)
    (hω' : ω * β * ω⁻¹ = α * β) (hω3 : ω ^ 3 = 1) {C : Subgroup J}
    (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hidx : C.index = 1 ∨ C.index = 2) : False := by
  have hωC : ω ∈ C := by
    rcases hidx with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      exact Subgroup.mem_top _
    · have h4 : ω = (ω ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hω3, one_mul]
      rw [h4]
      exact Subgroup.sq_mem_of_index_two h _
  have hone : α ∈ C ∨ β ∈ C ∨ α * β ∈ C := by
    rcases hidx with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      exact Or.inl (Subgroup.mem_top _)
    · by_cases ha : α ∈ C
      · exact Or.inl ha
      · by_cases hb : β ∈ C
        · exact Or.inr (Or.inl hb)
        · exact Or.inr (Or.inr ((Subgroup.mul_mem_iff_of_index_two h).2 (iff_of_false ha hb)))
  rcases hone with ha | hb | hab
  · have h1 : ω * α * ω⁻¹ = α := by rw [hC ω hωC α ha, mul_inv_cancel_right]
    exact hne (h1.symm.trans hω)
  · have h1 : ω * β * ω⁻¹ = β := by rw [hC ω hωC β hb, mul_inv_cancel_right]
    have h2 : α * β = β := hω'.symm.trans h1
    exact hα1 (by simpa using congrArg (fun x => x * β⁻¹) h2)
  · have h1 : ω * (α * β) * ω⁻¹ = α * β := by rw [hC ω hωC _ hab, mul_inv_cancel_right]
    have h2 : ω * (α * β) * ω⁻¹ = α := by
      calc ω * (α * β) * ω⁻¹ = (ω * α * ω⁻¹) * (ω * β * ω⁻¹) := by group
        _ = β * (α * β) := by rw [hω, hω']
        _ = α := by rw [← mul_assoc, ← hαβ, mul_assoc, ← pow_two, hβ, mul_one]
    exact hβ1 (by simpa using (h2.symm.trans h1).symm)

theorem false_of_tame_cases [Finite J] {α β ω : J} (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hne : α ≠ β)
    (hβ : β ^ 2 = 1) (hαβ : α * β = β * α) (hω : ω * α * ω⁻¹ = β)
    (hω' : ω * β * ω⁻¹ = α * β) (hω3 : ω ^ 3 = 1) (h16 : 16 ∣ Nat.card J)
    (hJ : IsCyclic J ∨ (∃ z : ℕ, Nonempty (J ≃* DihedralGroup z)) ∨ Nat.card J = 12 ∨
      Nat.card J = 24 ∨ Nonempty (J ≃* alternatingGroup (Fin 5))) : False := by
  rcases hJ with hcyc | ⟨z, ⟨e⟩⟩ | h12 | h24 | h60
  · exact false_of_abelian_index_le_two hα1 hβ1 hne hβ hαβ hω hω' hω3 (C := ⊤)
      (fun x _ y _ => IsMulCommutative.is_comm.comm x y) (Or.inl Subgroup.index_top)
  · have hz : z ≠ 0 := by
      rintro rfl
      have := Nat.card_congr e.toEquiv
      rw [DihedralGroup.nat_card] at this
      exact (Nat.card_pos (α := J)).ne' this
    haveI : NeZero z := ⟨hz⟩
    obtain ⟨C, hCcyc, hidx⟩ := CFSG.CGT.PushingUpLit.SolK.dihedral_cyclic_index z
    refine false_of_abelian_index_le_two hα1 hβ1 hne hβ hαβ hω hω' hω3
      (C := C.map (e.symm : DihedralGroup z →* J)) ?_ (Or.inr ?_)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : C) ⟨y, hy⟩))
    · rw [Subgroup.index_map_equiv C e.symm]
      exact hidx
  · omega
  · omega
  · obtain ⟨e⟩ := h60
    have : Nat.card J = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    omega

end Tame

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

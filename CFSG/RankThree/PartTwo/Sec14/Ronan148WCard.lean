module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJRank

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

theorem card_mul_card_le_of_inf_eq_bot {X : Type*} [Group X] [Finite X] {H K M : Subgroup X}
    (hHK : H ⊓ K = ⊥) (hH : H ≤ M) (hK : K ≤ M) :
    Nat.card H * Nat.card K ≤ Nat.card M := by
  let f : ↥H × ↥K → ↥M := fun p => ⟨(p.1 : X) * (p.2 : X), M.mul_mem (hH p.1.2) (hK p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨h, k⟩ ⟨h', k'⟩ heq
    have heq' : (h : X) * (k : X) = (h' : X) * (k' : X) := congrArg Subtype.val heq
    have hmem : (h' : X)⁻¹ * (h : X) = (k' : X) * (k : X)⁻¹ := by
      calc (h' : X)⁻¹ * (h : X) = (h' : X)⁻¹ * ((h : X) * (k : X)) * (k : X)⁻¹ := by group
        _ = (h' : X)⁻¹ * ((h' : X) * (k' : X)) * (k : X)⁻¹ := by rw [heq']
        _ = (k' : X) * (k : X)⁻¹ := by group
    have hI : (h' : X)⁻¹ * (h : X) ∈ H ⊓ K := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact H.mul_mem (H.inv_mem h'.2) h.2
      · rw [hmem]
        exact K.mul_mem k'.2 (K.inv_mem k.2)
    rw [hHK, Subgroup.mem_bot] at hI
    have hhh : (h : X) = (h' : X) := (inv_mul_eq_one.mp hI).symm
    have hkk : (k : X) = (k' : X) := by
      rw [hmem] at hI
      exact (mul_inv_eq_one.mp hI).symm
    exact Prod.ext (Subtype.ext hhh) (Subtype.ext hkk)
  have hle := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at hle

theorem exists_eq_sup_zpowers_of_card_le_nine {X : Type*} [Group X] [Finite X] {F : Subgroup X}
    {x : X} (hxF : x ∈ F) (hx1 : x ≠ 1) (hF3 : ∀ y ∈ F, y ^ 3 = 1)
    (hFc : ∀ y ∈ F, ∀ z ∈ F, y * z = z * y) (hF9 : Nat.card F ≤ 9) :
    ∃ j ∈ F, F = Subgroup.zpowers x ⊔ Subgroup.zpowers j := by
  by_cases h : F ≤ Subgroup.zpowers x
  · refine ⟨x, hxF, ?_⟩
    rw [sup_idem]
    exact le_antisymm h (Subgroup.zpowers_le.mpr hxF)
  · obtain ⟨j, hjF, hjx⟩ := SetLike.not_le_iff_exists.mp h
    have hSF : Subgroup.zpowers x ⊔ Subgroup.zpowers j ≤ F :=
      sup_le (Subgroup.zpowers_le.mpr hxF) (Subgroup.zpowers_le.mpr hjF)
    have hS9 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers j) = 9 :=
      CFSG.RankThree.PartTwo.Sec14.Ronan148J.card_zpowers_sup_zpowers_eq_nine
        (hFc x hxF j hjF) (hF3 x hxF) hx1 (hF3 j hjF) hjx
    have hEq : Subgroup.zpowers x ⊔ Subgroup.zpowers j = F :=
      Subgroup.eq_of_le_of_card_ge hSF (by rw [hS9]; exact hF9)
    exact ⟨j, hjF, hEq.symm⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148W

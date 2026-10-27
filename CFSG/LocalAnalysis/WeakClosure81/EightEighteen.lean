module

public import CFSG.LocalAnalysis.WeakClosure81.EightFifteen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem Sit813.eight_eighteen (hin : W3In814 G) {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : uGrp V K ⊓ centralizer (K : Set G) ≠ ⊥ := by
  intro hbot
  obtain ⟨hnat, -, h4⟩ := h.eight_fourteen hin
  have hD : ∀ u ∈ u1Grp V H T A K, u ∈ u1Grp V H T A K ⊓ centralizer (K : Set G) → u = 1 := by
    intro u hu hu'
    have hmem : u ∈ uGrp V K ⊓ centralizer (K : Set G) :=
      Subgroup.mem_inf.mpr ⟨Sit813.u1Grp_le_uGrp hu, (Subgroup.mem_inf.mp hu').2⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h16 : Nat.card (u1Grp V H T A K) = 16 := hnat.card_eq_sixteen hD
  have h16' : Set.ncard (u1Grp V H T A K : Set G) = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact h16
  obtain ⟨c, hcV, hc⟩ := Subgroup.relIndex_eq_two_iff.mp (h.relIndex_v1Grp h4)
  have hU₁V : ∀ a ∈ u1Grp V H T A K, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    h.isElemAbelian_uGrp.comm (Sit813.u1Grp_le_uGrp ha) (Sit813.V_le_uGrp hb)
  have hsub : (uGrp V K : Set G) ⊆
      (u1Grp V H T A K : Set G) ∪ (fun x => x * c⁻¹) '' (u1Grp V H T A K : Set G) := by
    intro u hu
    have hu' : u ∈ u1Grp V H T A K ⊔ V := by rwa [← h.eight_fifteen hin]
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm hU₁V hu'
    rcases hc b hb with ⟨h1, -⟩ | ⟨h1, -⟩
    · refine Or.inr ⟨a * (b * c), (u1Grp V H T A K).mul_mem ha
        (Sit813.v1Grp_le_u1Grp h1), ?_⟩
      group
    · exact Or.inl ((u1Grp V H T A K).mul_mem ha (Sit813.v1Grp_le_u1Grp h1))
  have hU32 : Set.ncard (uGrp V K : Set G) ≤ 32 := by
    calc Set.ncard (uGrp V K : Set G)
        ≤ Set.ncard ((u1Grp V H T A K : Set G) ∪
          (fun x => x * c⁻¹) '' (u1Grp V H T A K : Set G)) :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ Set.ncard (u1Grp V H T A K : Set G) +
          Set.ncard ((fun x => x * c⁻¹) '' (u1Grp V H T A K : Set G)) := Set.ncard_union_le _ _
      _ ≤ 16 + 16 := by
          have := Set.ncard_image_le (f := fun x : G => x * c⁻¹)
            (s := (u1Grp V H T A K : Set G)) (Set.toFinite _)
          omega
  have h64 := h.card_V_mul_card_V_le
  rw [h.card_V_eq_eight] at h64
  have hU : Nat.card (uGrp V K) = Set.ncard (uGrp V K : Set G) := Nat.card_coe_set_eq _
  omega

end CFSG.LocalAnalysis.WeakClosure81

end

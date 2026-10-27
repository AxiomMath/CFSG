module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Gen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Card
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_9_2_of {F : FanTree Γ G} {L : ZLab Γ G} (h65 : Fan65 F) (h512 : Fan512 F L)
    (h71a : Fan71a F L) (h71c : Fan71c F L) (h82a : Fan82a F L) (h83 : Fan83 F L)
    (h85 : Fan85 F L) (h86c : Fan86c F L) : Fan92 F L := by
  intro S
  have hrel := S.p1Rel_of F h71c h82a h83.2.1 h83.2.2.2.1 h85
  have hcard := FanTree.card_stabilizer_eq F h65 h71c S.D
  have hmem : ∀ g ∈ (({S.D.x, S.w, L.z S.α} : Set G) ∪ Set.range S.yEta ∪ Set.range S.zMu1),
      g ∈ MulAction.stabilizer G S.α := by
    rintro g ((hg | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact S.D.x_mem_stabilizer F h71c
      · exact S.w_mem_stabilizer
      · exact L.z_mem_stabilizer S.D.val
    · exact S.y_mem_stabilizer F h71c j
    · exact S.z_alpha_mem_stabilizer F h71c j
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hC2 : Nat.card S.D.calpha = 2 := by
      rw [hc] at hcard
      norm_num at hcard
      omega
    refine ⟨hrel, le_antisymm ((Subgroup.closure_le _).2 hmem) ?_⟩
    have hC := S.D.calpha_eq_zpowers_z F h71c h512 hC2
    refine S.stabilizer_le F h71c h512 h83.1 h86c (T := Subgroup.closure _) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Subgroup.subset_closure (Or.inl (Or.inl (by simp)))
    · exact Subgroup.subset_closure (Or.inl (Or.inl (by simp)))
    · exact Subgroup.subset_closure (Or.inl (Or.inl (by simp)))
    · exact fun j => Subgroup.subset_closure (Or.inl (Or.inr ⟨j, rfl⟩))
    · exact fun j => Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)
    · rw [hC]
      exact (Subgroup.zpowers_le).2 (Subgroup.subset_closure (Or.inl (Or.inl (by simp))))
  · have hC4 : Nat.card S.D.calpha = 4 := by
      rw [hc] at hcard
      norm_num at hcard
      omega
    have hmem' : ∀ g ∈ (({S.D.x, S.w, L.z S.α, S.c} : Set G) ∪ Set.range S.yEta ∪
        Set.range S.zMu1), g ∈ MulAction.stabilizer G S.α := by
      rintro g ((hg | ⟨j, rfl⟩) | ⟨j, rfl⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact S.D.x_mem_stabilizer F h71c
        · exact S.w_mem_stabilizer
        · exact L.z_mem_stabilizer S.D.val
        · exact S.c_mem_stabilizer F
      · exact S.y_mem_stabilizer F h71c j
      · exact S.z_alpha_mem_stabilizer F h71c j
    refine ⟨hrel, S.p1cRel_of F h71c h71a h512 h83.2.2.1 hC4, ?_,
      le_antisymm ((Subgroup.closure_le _).2 hmem') ?_⟩
    · rcases S.conj_c F hC4 with h1 | h1
      · left
        refine fcomm_eq_one_of_mul_comm ?_
        calc S.w * S.c = S.w * (S.w⁻¹ * S.c * S.w) := by rw [h1]
          _ = S.c * S.w := by group
      · right
        exact h1
    · refine S.stabilizer_le F h71c h512 h83.1 h86c (T := Subgroup.closure _) ?_ ?_ ?_ ?_ ?_ ?_
      · exact Subgroup.subset_closure (Or.inl (Or.inl (by simp)))
      · exact Subgroup.subset_closure (Or.inl (Or.inl (by simp)))
      · exact Subgroup.subset_closure (Or.inl (Or.inl (by simp)))
      · exact fun j => Subgroup.subset_closure (Or.inl (Or.inr ⟨j, rfl⟩))
      · exact fun j => Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)
      · rw [S.gen]
        exact (Subgroup.zpowers_le).2 (Subgroup.subset_closure (Or.inl (Or.inl (by simp))))

theorem fan_9_2 {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h65 : Fan65 F)
    (h512 : Fan512 F L) (h82 : Fan82 F L) (h83 : Fan83 F L) (h85 : Fan85 F L)
    (h86 : Fan86abc F L) : Fan92 F L :=
  fan_9_2_of h65 h512 h7.1 h7.2.2.1 h82.1 h83 h85 h86.2.2

end CFSG.Quasithin.Fan86

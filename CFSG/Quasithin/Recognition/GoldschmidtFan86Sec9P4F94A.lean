module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94Cnt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94S3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94T1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem zMu_mem_nbrStab_beta (F : FanTree Γ G) (h71c : Fan71c F L) (j : Fin 3) :
    S.zMu j ∈ nbrStab Γ G S.beta := by
  refine mem_nbrStab.2 fun w hw => ?_
  obtain ⟨i, rfl⟩ := (S.mem_neighborSet_beta_iff F).1 hw
  exact MulAction.mem_stabilizer_iff.1 (S.z_muV_mem_edge F h71c i j).1

theorem ballStab_three_le_nbrStab : ballStab Γ G 3 S.beta ≤ nbrStab Γ G S.beta :=
  S.ballStab_three_le_two.trans S.ballStab_two_le_nbrStab

theorem fan94a_of (F : FanTree Γ G) (h7 : Fan7 F L) (h65 : Fan65 F) (h81 : Fan81 F L)
    (h82 : Fan82 F L) (h83b : Fan83b F L) (h512 : Fan512 F L)
    (htop : 8 * Nat.card S.D.calpha ≤ (ballStab Γ G 2 S.beta).relIndex
      (Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta)) :
    nbrStab Γ G S.beta = Subgroup.closure (({S.w, S.wA 1, S.c, S.ub} : Set G) ∪
      Set.range S.zMu ∪ Set.range S.yMu ∪ Set.range S.zNb) ∧
    MulAction.stabilizer G S.beta =
      Subgroup.closure ({S.xβ, S.t} : Set G) ⊔ nbrStab Γ G S.beta := by
  have h71c : Fan71c F L := h7.2.2.1
  have hw := S.w_mem_nbrStab_beta F h71c
  have hwA := S.wA_mem_nbrStab_beta F h71c 1
  have hc := S.c_mem_nbrStab_beta F h7.1 h71c
  obtain ⟨e1, e2, e3⟩ := S.fan94b_of F h7 h65 h81 h82 h83b h512 hw hwA hc htop
  refine ⟨le_antisymm ?_ ?_, S.stabilizer_beta_eq F h71c h81⟩
  · rw [e1, e2, e3]
    refine sup_le ((Subgroup.closure_le _).2 ?_) (sup_le ((Subgroup.closure_le _).2 ?_)
      ((Subgroup.closure_le _).2 ?_))
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      all_goals exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (by simp))))
    · rintro g (rfl | ⟨i, rfl⟩)
      · have : S.ubs = S.zMu 0 * S.zMu 1 * S.zMu 2 * S.zNb 1 := rfl
        rw [this]
        refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
        · exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨0, rfl⟩)))
        · exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨1, rfl⟩)))
        · exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨2, rfl⟩)))
        · exact Subgroup.subset_closure (Or.inr ⟨1, rfl⟩)
      · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨i, rfl⟩))
    · rintro g (rfl | ⟨i, rfl⟩)
      · exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (by simp))))
      · exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  · refine (Subgroup.closure_le _).2 ?_
    rintro g (((hg | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact hw
      · exact hwA
      · exact hc
      · exact S.ballStab_three_le_nbrStab (S.ub_mem_ballStab_three F h71c h82.2.2)
    · exact S.zMu_mem_nbrStab_beta F h71c j
    · exact S.ballStab_two_le_nbrStab (S.yMu_mem_ballStab_two F h71c h81 j)
    · exact S.ballStab_three_le_nbrStab (S.zNb_mem_ballStab_three h71c j)

end Sec9Cfg

end CFSG.Quasithin.Fan86

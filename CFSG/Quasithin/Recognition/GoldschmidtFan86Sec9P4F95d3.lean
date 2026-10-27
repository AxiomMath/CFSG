module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95d2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Z2D

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem qv_loc (F : FanTree Γ G) (h7 : Fan7 F L) (h83a : Fan83a F L) (h83b : Fan83b F L) :
    ∃ m : Fin 5, m ≠ 0 ∧ m ≠ 2 ∧
      (S.qv = (S.dt F).alpha m ∨ S.qv = (S.dt F).alphaS F m) := by
  have h71c := h7.2.2.1
  have hZ := S.isZ2Pair_qv F h71c
  have hdist : Γ.dist ((S.xβ ^ 2)⁻¹ • S.α) S.qv = 2 := by
    rw [S.collar_one]
    exact hZ.2.2.2.2.1
  obtain ⟨m, hm⟩ := (S.dt F).exists_loc F h71c hdist
  refine ⟨m, ?_, ?_, hm⟩
  ·
    rintro rfl
    obtain ⟨δ'', hY⟩ := exists_isYPair h7 (S.dt F)
    have hnot := hZ.2.2.2.2.2.2.2
    rcases hm with hq | hq
    · apply hnot
      refine ⟨1, one_mem_gcirc' _ _, ?_⟩
      rw [one_smul, hq, S.dt_alpha_zero]
    · obtain ⟨y, hy, hyδ⟩ : ∃ y : G, y ∈ Gcirc Γ G (S.D.alpha 2) (S.D.beta 2) ∧
          y • S.D.delta 2 = (S.dt F).alphaS F 0 := by
        refine ⟨(S.dt F).y δ'' 1, ?_, ?_⟩
        · have h1 := D10Set.mem_gcirc_of_mem_nbrStab F ((S.dt F).adj_start_beta 2)
            ((S.dt F).y_mem_nbrStab F h83a hY 1)
          exact gcirc_congr S.collar_one (S.dt_beta_two F) h1
        · have hmove : (S.dt F).y δ'' 1 • (S.dt F).alpha 0 ≠ (S.dt F).alpha 0 := fun h' =>
            absurd (((S.dt F).y_fix_alpha_iff F h71c h83b hY 1 0).1 h') (by decide)
          rcases (S.dt F).perm_cases F ((S.dt F).y_mem_nbrStab F h83a hY 1) 0 with
            ⟨h1, -⟩ | ⟨h1, -⟩
          · exact absurd h1 hmove
          · rw [← S.dt_alpha_zero F]
            exact h1
      exact hnot ⟨y, hy, hyδ.trans hq.symm⟩
  ·
    rintro rfl
    have hadj : Γ.Adj ((S.dt F).beta 2) S.qv := by
      rcases hm with hq | hq
      · rw [hq]
        exact (S.dt F).adj_beta_alpha 2
      · rw [hq]
        exact (S.dt F).adj_beta_alphaS F 2
    rw [S.dt_beta_two] at hadj
    have h1 := F.isTree.connected.dist_triangle (u := S.α) (v := S.D.beta 2) (w := S.qv)
    have h2 : Γ.dist S.α (S.D.beta 2) = 1 := dist_eq_one_iff_adj.2 (S.D.adj_start_beta 2)
    have h3 : Γ.dist (S.D.beta 2) S.qv = 1 := dist_eq_one_iff_adj.2 hadj
    have h4 := hZ.2.2.2.2.2.2.1
    omega

end Sec9Cfg

end CFSG.Quasithin.Fan86

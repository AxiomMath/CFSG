module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2cA
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2cBall
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94Arm

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem w_mem_nbrStab_beta (F : FanTree Γ G) (_h71c : Fan71c F L) : S.w ∈ nbrStab Γ G S.beta := by
  have h := (Arc.mem_stab G).1 S.isW1.fixes
  have h0 : S.w • S.α = S.α := by
    have := h 0 (by norm_num)
    rwa [S.D.start 2] at this
  have h2 : S.w • S.D.alpha 2 = S.D.alpha 2 := h 2 (by norm_num)
  exact F.fix_two_nbrs (S.D.adj_start_beta 2).symm (S.D.adj_beta_alpha 2)
    (S.D.alpha_ne_start 2).symm h0 h2

theorem wA_mem_nbrStab_beta (F : FanTree Γ G) (h71c : Fan71c F L) (i : Fin 3) :
    S.wA i ∈ nbrStab Γ G S.beta := by
  have hg : (S.xβ ^ (i : ℕ))⁻¹ ∈ MulAction.stabilizer G S.beta :=
    MulAction.mem_stabilizer_iff.2 (S.xβ_pow_inv_smul_beta _)
  have := F.conj_mem_nbrStab_of_stab hg (S.w_mem_nbrStab_beta F h71c)
  rwa [inv_inv] at this

theorem c_mem_nbrStab_beta (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) :
    S.c ∈ nbrStab Γ G S.beta := by
  have hc : S.c ∈ S.D.calpha := by
    rw [S.gen]
    exact Subgroup.mem_zpowers _
  have h0 : S.c • S.α = S.α := by
    have := S.D.fix_of_mem_calpha F h71a h71c hc 2 (m := 0) (by norm_num)
    rwa [S.D.start 2] at this
  have h2 : S.c • S.D.alpha 2 = S.D.alpha 2 :=
    S.D.fix_of_mem_calpha F h71a h71c hc 2 (m := 2) (by norm_num)
  exact F.fix_two_nbrs (S.D.adj_start_beta 2).symm (S.D.adj_beta_alpha 2)
    (S.D.alpha_ne_start 2).symm h0 h2

theorem calpha_inf_nbrStab_alphaV_one_le (F : FanTree Γ G) (h7 : Fan7 F L) (_h81 : Fan81 F L)
    (_h512 : Fan512 F L) {g : G} (hg : g ∈ S.D.calpha) (hK : g ∈ nbrStab Γ G (S.alphaV 1)) :
    g ∈ Subgroup.zpowers (L.z S.α) := by
  have h0 : g ∈ nbrStab Γ G (S.alphaV 0) := by
    rw [S.alphaV_zero]
    exact (Subgroup.mem_inf.1 hg).1
  have h2 : g ∈ nbrStab Γ G (S.alphaV 2) := by
    rw [S.alphaV_two]
    exact P2c.calpha_mem_nbrStab_alpha S.D h7 hg 2
  have hb2 : g ∈ ballStab Γ G 2 (S.D.beta 2) := by
    refine (S.mem_ballStab_two_beta_iff F).2 fun i => ?_
    fin_cases i
    exacts [h0, hK, h2]
  exact P2c.calpha_mem_zpowers S.D h7 hg hb2

end Sec9Cfg

end CFSG.Quasithin.Fan86

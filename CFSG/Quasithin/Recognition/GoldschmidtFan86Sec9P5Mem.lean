module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Star

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G}

namespace Sec9Cfg

variable (S : Sec9Cfg L)

theorem adj_alpha_beta : Γ.Adj S.α S.beta := S.D.adj_start_beta 2

theorem xb_mem : S.xβ ∈ MulAction.stabilizer G S.beta :=
  MulAction.mem_stabilizer_iff.2 S.isBeta.fixβ

theorem w_mem : S.w ∈ MulAction.stabilizer G S.α := by
  have := (Arc.mem_stab G).1 S.isW1.fixes 0 (by norm_num)
  rw [S.D.start 2] at this
  exact this

theorem za_mem : L.z S.α ∈ MulAction.stabilizer G S.α := L.z_mem_stabilizer S.D.val

theorem c_mem (F : FanTree Γ G) : S.c ∈ MulAction.stabilizer G S.α :=
  F.nbrStab_le_stabilizer S.α (Subgroup.mem_inf.1 S.c_mem_calpha_gen).1

variable (H : P5Hyp F L)

include H

theorem x_mem : S.D.x ∈ MulAction.stabilizer G S.α := S.D.x_mem_stabilizer F H.h7.2.2.1

theorem yEta_mem (j : Fin 5) : S.yEta j ∈ nbrStab Γ G S.α := by
  have h := (H.h8.fan83a S.α S.D S.η' S.isBeta.pair)
  rw [h]
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨j, rfl⟩)

theorem zMu1_mem (j : Fin 5) : S.zMu1 j ∈ MulAction.stabilizer G S.α := by
  refine (H.h7.2.2.1.z_mem_stabilizer_iff (S.D.valence_alpha F j) S.α).2 ?_
  have : Γ.dist S.α (S.D.alpha j) = 2 := S.D.dist_vert F j (m := 2) (by norm_num)
  rw [SimpleGraph.dist_comm, this]
  norm_num

theorem t_mem : S.t ∈ MulAction.stabilizer G S.beta :=
  MulAction.mem_stabilizer_iff.2
    (mem_nbrStab.1 (S.yEta_mem H 0) S.beta S.adj_alpha_beta)

theorem nbrBeta_gens :
    nbrStab Γ G S.beta = Subgroup.closure (({S.w, S.wA 1, S.c, S.ub} : Set G) ∪
      Set.range S.zMu ∪ Set.range S.yMu ∪ Set.range S.zNb) := (H.h94.1 S).1

theorem mem_nbrBeta {g : G} (hg : g ∈ (({S.w, S.wA 1, S.c, S.ub} : Set G) ∪
      Set.range S.zMu ∪ Set.range S.yMu ∪ Set.range S.zNb)) : g ∈ nbrStab Γ G S.beta := by
  rw [S.nbrBeta_gens H]
  exact Subgroup.subset_closure hg

theorem w_mem_beta : S.w ∈ nbrStab Γ G S.beta := S.mem_nbrBeta H (by simp)

theorem wA1_mem_beta : S.wA 1 ∈ nbrStab Γ G S.beta := S.mem_nbrBeta H (by simp)

theorem c_mem_beta : S.c ∈ nbrStab Γ G S.beta := S.mem_nbrBeta H (by simp)

theorem ub_mem_beta : S.ub ∈ nbrStab Γ G S.beta := S.mem_nbrBeta H (by simp)

theorem zMu_mem_beta (i : Fin 3) : S.zMu i ∈ nbrStab Γ G S.beta :=
  S.mem_nbrBeta H (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))

theorem yMu_mem_beta (i : Fin 3) : S.yMu i ∈ nbrStab Γ G S.beta :=
  S.mem_nbrBeta H (Or.inl (Or.inr ⟨i, rfl⟩))

theorem zNb_mem_beta (i : Fin 3) : S.zNb i ∈ nbrStab Γ G S.beta :=
  S.mem_nbrBeta H (Or.inr ⟨i, rfl⟩)

theorem t_not_mem_nbrBeta : S.t ∉ nbrStab Γ G S.beta := by
  intro ht
  have htα : S.t • S.α = S.α :=
    MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer S.α (S.yEta_mem H 0))
  have hadj : Γ.Adj S.beta S.α := S.adj_alpha_beta.symm
  have h1 : Γ.Adj S.beta (S.xβ • S.α) := F.adj_smul_of_mem_stabilizer (S.xb_mem) hadj
  have e1 : S.t⁻¹ • (S.xβ • S.α) = S.xβ • S.α := mem_nbrStab.1 (inv_mem ht) _ h1
  have e3 : (S.t⁻¹ * S.xβ * S.t) • S.α = S.xβ • S.α := by
    rw [mul_smul, mul_smul, htα, e1]
  have e2 : (S.t⁻¹ * S.xβ * S.t) • S.α = S.xβ⁻¹ • S.α := by
    rw [show S.t⁻¹ * S.xβ * S.t = S.xβ⁻¹ from S.isBeta.inverts]
  have e4 : (S.xβ ^ 2) • S.α = S.α := by
    have : S.xβ • S.α = S.xβ⁻¹ • S.α := e3.symm.trans e2
    calc (S.xβ ^ 2) • S.α = S.xβ • (S.xβ • S.α) := by rw [pow_two, mul_smul]
      _ = S.xβ • (S.xβ⁻¹ • S.α) := by rw [this]
      _ = S.α := by simp
  have hcol := S.isBeta.collar 1 (by norm_num)
  have e5 : (S.xβ ^ 2)⁻¹ • S.α = S.α := by
    rw [inv_smul_eq_iff, e4]
  have e6 : S.D.bv S.xβ 2 1 = S.α := by
    unfold D10Set.bv
    simpa [S.D.start 0] using e5
  rw [e6] at hcol
  refine (S.D.P 2).nb 0 (by norm_num) ?_
  rw [S.D.start 2]
  exact hcol

end Sec9Cfg

end CFSG.Quasithin.Fan86

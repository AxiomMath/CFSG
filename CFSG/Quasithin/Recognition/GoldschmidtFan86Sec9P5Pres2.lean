module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Pres1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Mem
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Main1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg4

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G}

namespace Sec9Cfg

variable (S : Sec9Cfg L) (H : P5Hyp F L)

include H

theorem exists_ids (hS : S.Star) :
    ∃ e : ℕ, e ≤ 1 ∧ P5Ids S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t (S.wA 1) S.ub S.zMu S.yMu S.zNb
      e e := by
  obtain ⟨e₁, e₂, hw2⟩ := fan_9_10b H S hS
  have hids := S.ids H hS (e₁ := (e₁ : ℕ)) (e₂ := (e₂ : ℕ)) (by omega) (by omega) hw2
  have hz2 : S.zMu1 2 ≠ 1 := L.z_ne_one (S.D.valence_alpha F 2)
  have heq : (e₁ : ℕ) = (e₂ : ℕ) := hids.exp_eq (S.p1Rel H) hz2
  rw [← heq] at hids
  exact ⟨e₁, by omega, hids⟩

theorem nbrBeta_le {K : Subgroup G} (hw : S.w ∈ K) (hw2 : S.wA 1 ∈ K) (hc : S.c ∈ K)
    (hub : S.ub ∈ K) (hzm : ∀ i, S.zMu i ∈ K) (hym : ∀ i, S.yMu i ∈ K)
    (hza : ∀ i, S.zNb i ∈ K) : nbrStab Γ G S.beta ≤ K := by
  rw [S.nbrBeta_gens H]
  refine (Subgroup.closure_le K).2 ?_
  rintro g ((((rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  exacts [hw, hw2, hc, hub, hzm i, hym i, hza i]

theorem edge_eq {K : Subgroup G} (hK : nbrStab Γ G S.beta ≤ K) (ht : S.t ∈ K)
    (hle : K ≤ MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta) :
    K = MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta := by
  have h2 := F.relIndex_nbrStab_eq_two S.adj_alpha_beta.symm (S.D.valence_beta F 2)
  rw [inf_comm] at hle ⊢
  exact eq_of_relIndex_two hK hle h2 ht (S.t_not_mem_nbrBeta H)

theorem za_mem_beta : L.z S.α ∈ nbrStab Γ G S.beta := by
  obtain ⟨-, -, -, a4, -, -, -, -, -, -⟩ := H.h95.2.2.2 S
  rw [← a4]
  exact S.zNb_mem_beta H 0

end Sec9Cfg

end CFSG.Quasithin.Fan86

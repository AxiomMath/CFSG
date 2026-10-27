module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Pres3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G}

namespace Sec9Cfg

variable (S : Sec9Cfg L) (H : P5Hyp F L)

@[expose] def gensA12 (e d : ℕ) : Set G :=
  ({S.D.x, S.w * L.z S.α ^ e, L.z S.α, S.c * L.z S.α ^ d} : Set G) ∪ Set.range S.yEta ∪
    Set.range S.zMu1

@[expose] def gensB12 (e d : ℕ) : Set G :=
  ({S.xβ, S.t, S.w * L.z S.α ^ e, S.wA 1 * S.zNb 1 ^ e, S.ub, S.c * L.z S.α ^ d} : Set G) ∪
    Set.range S.zMu ∪ Set.range S.yMu ∪ Set.range S.zNb

@[expose] def gensE12 (e d : ℕ) : Set G :=
  ({S.t, S.w * L.z S.α ^ e, S.wA 1 * S.zNb 1 ^ e, S.ub, S.c * L.z S.α ^ d} : Set G) ∪
    Set.range S.zMu ∪ Set.range S.yMu ∪ Set.range S.zNb

theorem cN_mem_alpha (F : FanTree Γ G) (d : ℕ) :
    S.c * L.z S.α ^ d ∈ MulAction.stabilizer G S.α :=
  (MulAction.stabilizer G S.α).mul_mem (S.c_mem F)
    ((MulAction.stabilizer G S.α).pow_mem S.za_mem d)

theorem gensE12_subset (e d : ℕ) : S.gensE12 e d ⊆ S.gensB12 e d := by
  rintro g ((((rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  all_goals (unfold gensB12; memsimp)

include H

theorem z_ne : L.z S.α ≠ 1 ∧ S.zMu1 2 ≠ 1 ∧ S.zMu1 2 ≠ L.z S.α :=
  ⟨L.z_ne_one S.D.val, L.z_ne_one (S.D.valence_alpha F 2), fun h =>
    S.D.alpha_ne_start 2 (H.h7.2.2.1.z_injective (S.D.valence_alpha F 2) S.D.val h)⟩

theorem cN_mem_beta (d : ℕ) : S.c * L.z S.α ^ d ∈ nbrStab Γ G S.beta :=
  (nbrStab Γ G S.beta).mul_mem (S.c_mem_beta H)
    ((nbrStab Γ G S.beta).pow_mem (S.za_mem_beta H) d)

theorem memA12 (e d : ℕ) : ∀ g ∈ S.gensA12 e d, g ∈ MulAction.stabilizer G S.α := by
  obtain ⟨hwa, hya, hza⟩ := S.base_mem_alpha (e := e) H
  rintro g (((rfl | rfl | rfl | rfl) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  exacts [S.x_mem H, hwa, S.za_mem, S.cN_mem_alpha F d, hya j, hza j]

theorem memB12 (e d : ℕ) : ∀ g ∈ S.gensB12 e d, g ∈ MulAction.stabilizer G S.beta := by
  rintro g ((((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  exacts [S.xb_mem, S.t_mem H, F.nbrStab_le_stabilizer _ (S.wN_mem_beta H),
    F.nbrStab_le_stabilizer _ (S.w2N_mem_beta H), F.nbrStab_le_stabilizer _ (S.ub_mem_beta H),
    F.nbrStab_le_stabilizer _ (S.cN_mem_beta H d),
    F.nbrStab_le_stabilizer _ (S.zMu_mem_beta H i), F.nbrStab_le_stabilizer _ (S.yMu_mem_beta H i),
    F.nbrStab_le_stabilizer _ (S.zNb_mem_beta H i)]

theorem memE12 {e : ℕ} (d : ℕ)
    (hid : P5Ids S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t (S.wA 1) S.ub S.zMu S.yMu S.zNb e e) :
    ∀ g ∈ S.gensE12 e d, g ∈ MulAction.stabilizer G S.α := by
  obtain ⟨hwa, hya, hza⟩ := S.base_mem_alpha (e := e) H
  obtain ⟨ht_a, hw2_a, hub_a, hzm_a, hym_a, hza'_a⟩ :=
    (hid.normalize (S.p1Rel H)).mem_of_gens hwa S.za_mem hya hza
  rintro g ((((rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  exacts [ht_a, hwa, hw2_a, hub_a, S.cN_mem_alpha F d, hzm_a i, hym_a i, hza'_a i]

theorem c_mem_closure {d : ℕ} (hd : d ≤ 1) {T : Set G} (hcT : S.c * L.z S.α ^ d ∈ T)
    (hzn : ∀ i, S.zNb i ∈ T) : S.c ∈ Subgroup.closure T := by
  have hz : L.z S.α * L.z S.α = 1 := L.z_mul_self S.D.val
  have hza : L.z S.α ∈ Subgroup.closure T := by
    rw [← S.zNb0_eq H]
    exact Subgroup.subset_closure (hzn 0)
  have h3 := mul_mem (Subgroup.subset_closure hcT) (pow_mem hza d)
  rwa [mul_pow_pow_cancel S.c _ hz hd] at h3

theorem genA12 {e d : ℕ} (he : e ≤ 1) (hd : d ≤ 1)
    (hcard : Nat.card (MulAction.stabilizer G S.α) = 5 * 2 ^ 12) :
    Subgroup.closure (S.gensA12 e d) = MulAction.stabilizer G S.α := by
  have hz : L.z S.α * L.z S.α = 1 := L.z_mul_self S.D.val
  refine le_antisymm ((Subgroup.closure_le _).2 (S.memA12 H e d)) ?_
  rw [← ((H.h92 S).2 hcard).2.2.2]
  have hza : L.z S.α ∈ Subgroup.closure (S.gensA12 e d) :=
    Subgroup.subset_closure (by unfold gensA12; memsimp)
  refine (Subgroup.closure_le _).2 ?_
  rintro g ((((rfl | rfl | rfl | rfl) | ⟨j, rfl⟩) | ⟨j, rfl⟩))
  · exact Subgroup.subset_closure (by unfold gensA12; memsimp)
  · have h1 : S.w * L.z S.α ^ e ∈ Subgroup.closure (S.gensA12 e d) :=
      Subgroup.subset_closure (by unfold gensA12; memsimp)
    have h3 := mul_mem h1 (pow_mem hza e)
    rwa [mul_pow_pow_cancel S.w _ hz he] at h3
  · exact Subgroup.subset_closure (by unfold gensA12; memsimp)
  · have h1 : S.c * L.z S.α ^ d ∈ Subgroup.closure (S.gensA12 e d) :=
      Subgroup.subset_closure (by unfold gensA12; memsimp)
    have h3 := mul_mem h1 (pow_mem hza d)
    rwa [mul_pow_pow_cancel S.c _ hz hd] at h3
  · exact Subgroup.subset_closure (by unfold gensA12; memsimp)
  · exact Subgroup.subset_closure (by unfold gensA12; memsimp)

theorem genB12 {e d : ℕ} (he : e ≤ 1) (hd : d ≤ 1) :
    Subgroup.closure (S.gensB12 e d) = MulAction.stabilizer G S.beta := by
  refine le_antisymm ((Subgroup.closure_le _).2 (S.memB12 H e d)) ?_
  rw [(H.h94.1 S).2]
  refine sup_le ((Subgroup.closure_le _).2 ?_) (S.nbrBeta_le_closure' H he
    (S.c_mem_closure H hd (by unfold gensB12; memsimp) (fun i => by unfold gensB12; memsimp))
    (by unfold gensB12; memsimp) (by unfold gensB12; memsimp) (by unfold gensB12; memsimp)
    (fun i => by unfold gensB12; memsimp) (fun i => by unfold gensB12; memsimp)
    (fun i => by unfold gensB12; memsimp))
  rintro g (rfl | rfl)
  · exact Subgroup.subset_closure (by unfold gensB12; memsimp)
  · exact Subgroup.subset_closure (by unfold gensB12; memsimp)

theorem genE12 {e d : ℕ} (he : e ≤ 1) (hd : d ≤ 1)
    (hid : P5Ids S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t (S.wA 1) S.ub S.zMu S.yMu S.zNb e e) :
    Subgroup.closure (S.gensE12 e d) =
      MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta := by
  have hle : Subgroup.closure (S.gensE12 e d) ≤
      MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta :=
    (Subgroup.closure_le _).2 fun g hg =>
      ⟨S.memE12 H d hid g hg, S.memB12 H e d g (S.gensE12_subset e d hg)⟩
  exact S.edge_eq H (S.nbrBeta_le_closure' H he
    (S.c_mem_closure H hd (by unfold gensE12; memsimp) (fun i => by unfold gensE12; memsimp))
    (by unfold gensE12; memsimp) (by unfold gensE12; memsimp) (by unfold gensE12; memsimp)
    (fun i => by unfold gensE12; memsimp) (fun i => by unfold gensE12; memsimp)
    (fun i => by unfold gensE12; memsimp)) (Subgroup.subset_closure (by unfold gensE12; memsimp))
    hle

end Sec9Cfg

end CFSG.Quasithin.Fan86

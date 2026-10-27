module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Pres2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G}

theorem mul_pow_pow_cancel {H : Type*} [Group H] (w za : H) (hz : za * za = 1) {e : ℕ}
    (he : e ≤ 1) : w * za ^ e * za ^ e = w := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with rfl | rfl
  · simp
  · rw [pow_one, mul_assoc, hz, mul_one]

namespace Sec9Cfg

variable (S : Sec9Cfg L) (H : P5Hyp F L)

theorem zNb_mul_self (i : Fin 3) : S.zNb i * S.zNb i = 1 := by
  rw [S.zNb_eq i]
  have hz : L.z S.α * L.z S.α = 1 := L.z_mul_self S.D.val
  calc (S.xβ ^ (i : ℕ))⁻¹ * L.z S.α * S.xβ ^ (i : ℕ) *
        ((S.xβ ^ (i : ℕ))⁻¹ * L.z S.α * S.xβ ^ (i : ℕ))
      = (S.xβ ^ (i : ℕ))⁻¹ * (L.z S.α * L.z S.α) * S.xβ ^ (i : ℕ) := by group
    _ = 1 := by rw [hz]; group

@[expose] def gensA11 (e : ℕ) : Set G :=
  ({S.D.x, S.w * L.z S.α ^ e, L.z S.α} : Set G) ∪ Set.range S.yEta ∪ Set.range S.zMu1

@[expose] def gensB11 (e : ℕ) : Set G :=
  ({S.xβ, S.t, S.w * L.z S.α ^ e, S.wA 1 * S.zNb 1 ^ e, S.ub} : Set G) ∪ Set.range S.zMu ∪
    Set.range S.yMu ∪ Set.range S.zNb

@[expose] def gensE11 (e : ℕ) : Set G :=
  ({S.t, S.w * L.z S.α ^ e, S.wA 1 * S.zNb 1 ^ e, S.ub} : Set G) ∪ Set.range S.zMu ∪
    Set.range S.yMu ∪ Set.range S.zNb

theorem base_mem_alpha {e : ℕ} (H : P5Hyp F L) :
    (S.w * L.z S.α ^ e ∈ MulAction.stabilizer G S.α) ∧
      (∀ j, S.yEta j ∈ MulAction.stabilizer G S.α) ∧
      ∀ j, S.zMu1 j ∈ MulAction.stabilizer G S.α :=
  ⟨(MulAction.stabilizer G S.α).mul_mem S.w_mem
      ((MulAction.stabilizer G S.α).pow_mem S.za_mem e),
    fun j => F.nbrStab_le_stabilizer S.α (S.yEta_mem H j), S.zMu1_mem H⟩

theorem gensE11_subset (e : ℕ) : S.gensE11 e ⊆ S.gensB11 e := by
  rintro g ((((rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  all_goals (unfold gensB11; memsimp)

include H

theorem wN_mem_beta {e : ℕ} : S.w * L.z S.α ^ e ∈ nbrStab Γ G S.beta :=
  (nbrStab Γ G S.beta).mul_mem (S.w_mem_beta H) ((nbrStab Γ G S.beta).pow_mem (S.za_mem_beta H) e)

theorem w2N_mem_beta {e : ℕ} : S.wA 1 * S.zNb 1 ^ e ∈ nbrStab Γ G S.beta :=
  (nbrStab Γ G S.beta).mul_mem (S.wA1_mem_beta H)
    ((nbrStab Γ G S.beta).pow_mem (S.zNb_mem_beta H 1) e)

theorem memA11 (e : ℕ) : ∀ g ∈ S.gensA11 e, g ∈ MulAction.stabilizer G S.α := by
  obtain ⟨hwa, hya, hza⟩ := S.base_mem_alpha (e := e) H
  rintro g (((rfl | rfl | rfl) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  exacts [S.x_mem H, hwa, S.za_mem, hya j, hza j]

theorem memB11 (e : ℕ) : ∀ g ∈ S.gensB11 e, g ∈ MulAction.stabilizer G S.beta := by
  rintro g ((((rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  exacts [S.xb_mem, S.t_mem H, F.nbrStab_le_stabilizer _ (S.wN_mem_beta H),
    F.nbrStab_le_stabilizer _ (S.w2N_mem_beta H), F.nbrStab_le_stabilizer _ (S.ub_mem_beta H),
    F.nbrStab_le_stabilizer _ (S.zMu_mem_beta H i), F.nbrStab_le_stabilizer _ (S.yMu_mem_beta H i),
    F.nbrStab_le_stabilizer _ (S.zNb_mem_beta H i)]

theorem memE11 {e : ℕ}
    (hid : P5Ids S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t (S.wA 1) S.ub S.zMu S.yMu S.zNb e e) :
    ∀ g ∈ S.gensE11 e, g ∈ MulAction.stabilizer G S.α := by
  obtain ⟨hwa, hya, hza⟩ := S.base_mem_alpha (e := e) H
  obtain ⟨ht_a, hw2_a, hub_a, hzm_a, hym_a, hza'_a⟩ :=
    (hid.normalize (S.p1Rel H)).mem_of_gens hwa S.za_mem hya hza
  rintro g ((((rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  exacts [ht_a, hwa, hw2_a, hub_a, hzm_a i, hym_a i, hza'_a i]

theorem zNb0_eq : S.zNb 0 = L.z S.α := (H.h95.2.2.2 S).2.2.2.1

theorem nbrBeta_le_closure' {e : ℕ} (he : e ≤ 1) {T : Set G}
    (hc : S.c ∈ Subgroup.closure T) (hwN : S.w * L.z S.α ^ e ∈ T)
    (hw2N : S.wA 1 * S.zNb 1 ^ e ∈ T) (hub : S.ub ∈ T) (hzm : ∀ i, S.zMu i ∈ T)
    (hym : ∀ i, S.yMu i ∈ T) (hzn : ∀ i, S.zNb i ∈ T) :
    nbrStab Γ G S.beta ≤ Subgroup.closure T := by
  have hz : L.z S.α * L.z S.α = 1 := L.z_mul_self S.D.val
  have hza : L.z S.α ∈ Subgroup.closure T := by
    rw [← S.zNb0_eq H]
    exact Subgroup.subset_closure (hzn 0)
  refine S.nbrBeta_le H ?_ ?_ hc ?_ (fun i => Subgroup.subset_closure (hzm i))
    (fun i => Subgroup.subset_closure (hym i)) (fun i => Subgroup.subset_closure (hzn i))
  · rw [← mul_pow_pow_cancel S.w _ hz he]
    exact mul_mem (Subgroup.subset_closure hwN) (pow_mem hza e)
  · rw [← mul_pow_pow_cancel (S.wA 1) (S.zNb 1) (S.zNb_mul_self 1) he]
    exact mul_mem (Subgroup.subset_closure hw2N) (pow_mem (Subgroup.subset_closure (hzn 1)) e)
  · exact Subgroup.subset_closure hub

theorem c_eq_za (hS : S.Star) (h2 : Nat.card S.D.calpha = 2) : S.c = L.z S.α := by
  rw [← S.zNb0_eq H]
  exact (fan_9_12 H S hS).2.2 h2

theorem genA11 {e : ℕ} (he : e ≤ 1)
    (hcard : Nat.card (MulAction.stabilizer G S.α) = 5 * 2 ^ 11) :
    Subgroup.closure (S.gensA11 e) = MulAction.stabilizer G S.α := by
  have hz : L.z S.α * L.z S.α = 1 := L.z_mul_self S.D.val
  refine le_antisymm ((Subgroup.closure_le _).2 (S.memA11 H e)) ?_
  rw [← ((H.h92 S).1 hcard).2]
  refine (Subgroup.closure_le _).2 ?_
  rintro g (((rfl | rfl | rfl) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inl rfl)))
  · have h1 : S.w * L.z S.α ^ e ∈ Subgroup.closure (S.gensA11 e) :=
      Subgroup.subset_closure (by unfold gensA11; memsimp)
    have h2 : L.z S.α ∈ Subgroup.closure (S.gensA11 e) :=
      Subgroup.subset_closure (by unfold gensA11; memsimp)
    have h3 := mul_mem h1 (pow_mem h2 e)
    rwa [mul_pow_pow_cancel S.w _ hz he] at h3
  · exact Subgroup.subset_closure (by unfold gensA11; memsimp)
  · exact Subgroup.subset_closure (by unfold gensA11; memsimp)
  · exact Subgroup.subset_closure (by unfold gensA11; memsimp)

theorem genB11 {e : ℕ} (he : e ≤ 1) (hcza : S.c = L.z S.α) :
    Subgroup.closure (S.gensB11 e) = MulAction.stabilizer G S.beta := by
  refine le_antisymm ((Subgroup.closure_le _).2 (S.memB11 H e)) ?_
  rw [(H.h94.1 S).2]
  have hc : S.c ∈ Subgroup.closure (S.gensB11 e) := by
    rw [hcza, ← S.zNb0_eq H]
    exact Subgroup.subset_closure (by unfold gensB11; memsimp)
  refine sup_le ((Subgroup.closure_le _).2 ?_) (S.nbrBeta_le_closure' H he hc
    (by unfold gensB11; memsimp) (by unfold gensB11; memsimp) (by unfold gensB11; memsimp)
    (fun i => by unfold gensB11; memsimp) (fun i => by unfold gensB11; memsimp)
    (fun i => by unfold gensB11; memsimp))
  rintro g (rfl | rfl)
  · exact Subgroup.subset_closure (by unfold gensB11; memsimp)
  · exact Subgroup.subset_closure (by unfold gensB11; memsimp)

theorem genE11 {e : ℕ} (he : e ≤ 1) (hcza : S.c = L.z S.α)
    (hid : P5Ids S.w (L.z S.α) S.yEta S.zMu1 S.xβ S.t (S.wA 1) S.ub S.zMu S.yMu S.zNb e e) :
    Subgroup.closure (S.gensE11 e) =
      MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta := by
  have hle : Subgroup.closure (S.gensE11 e) ≤
      MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta := by
    exact (Subgroup.closure_le _).2 fun g hg =>
      ⟨S.memE11 H hid g hg, S.memB11 H e g (S.gensE11_subset e hg)⟩
  have hc : S.c ∈ Subgroup.closure (S.gensE11 e) := by
    rw [hcza, ← S.zNb0_eq H]
    exact Subgroup.subset_closure (by unfold gensE11; memsimp)
  exact S.edge_eq H (S.nbrBeta_le_closure' H he hc (by unfold gensE11; memsimp)
    (by unfold gensE11; memsimp) (by unfold gensE11; memsimp) (fun i => by unfold gensE11; memsimp)
    (fun i => by unfold gensE11; memsimp) (fun i => by unfold gensE11; memsimp))
    (Subgroup.subset_closure (by unfold gensE11; memsimp)) hle

end Sec9Cfg

end CFSG.Quasithin.Fan86

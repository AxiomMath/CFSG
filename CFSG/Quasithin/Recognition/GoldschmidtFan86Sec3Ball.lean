module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Star

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem dist_le_two_iff (hc : Γ.Connected) {α w : V} :
    Γ.dist α w ≤ 2 ↔ w = α ∨ Γ.Adj α w ∨ ∃ γ, Γ.Adj α γ ∧ Γ.Adj γ w := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist α w
    rw [← hp] at h
    match p, h with
    | .nil, _ => exact Or.inl rfl
    | .cons h1 .nil, _ => exact Or.inr (Or.inl h1)
    | .cons h1 (.cons h2 .nil), _ => exact Or.inr (Or.inr ⟨_, h1, h2⟩)
    | .cons _ (.cons _ (.cons _ q)), h' =>
      exfalso
      simp only [Walk.length_cons] at h'
      omega
  · rintro (rfl | h | ⟨γ, h1, h2⟩)
    · simp
    · exact (dist_le (Walk.cons h .nil)).trans (by simp)
    · exact (dist_le (Walk.cons h1 (Walk.cons h2 .nil))).trans (by simp)

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem mem_ballStab_two_iff {α : V} {g : G} :
    g ∈ ballStab Γ G 2 α ↔ g ∈ nbrStab Γ G α ∧ ∀ γ, Γ.Adj α γ → g ∈ nbrStab Γ G γ := by
  have hc := F.isTree.connected
  constructor
  · intro h
    refine ⟨mem_nbrStab.2 fun w hw => mem_ballStab.1 h w ?_, fun γ hγ => mem_nbrStab.2 fun w hw =>
      mem_ballStab.1 h w ?_⟩
    · exact (dist_le_two_iff hc).2 (Or.inr (Or.inl hw))
    · exact (dist_le_two_iff hc).2 (Or.inr (Or.inr ⟨γ, hγ, hw⟩))
  · rintro ⟨h1, h2⟩
    rw [mem_ballStab]
    intro w hw
    rcases (dist_le_two_iff hc).1 hw with h0 | hw | ⟨γ, hγ, hw⟩
    · rw [h0]
      exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α h1)
    · exact mem_nbrStab.1 h1 w hw
    · exact mem_nbrStab.1 (h2 γ hγ) w hw

theorem ballStab_two_le_inf {α β : V} (hαβ : Γ.Adj α β) :
    ballStab Γ G 2 α ≤ nbrStab Γ G α ⊓ nbrStab Γ G β := fun _ hg =>
  ⟨((F.mem_ballStab_two_iff).1 hg).1, ((F.mem_ballStab_two_iff).1 hg).2 β hαβ⟩

theorem conj_mem_ballStab_two {α : V} {g : G} (hg : g ∈ MulAction.stabilizer G α) {h : G}
    (hh : h ∈ ballStab Γ G 2 α) : g * h * g⁻¹ ∈ ballStab Γ G 2 α := by
  rw [F.mem_ballStab_two_iff] at hh ⊢
  refine ⟨F.conj_mem_nbrStab_of_stab hg hh.1, fun γ hγ => ?_⟩
  have hγ' : Γ.Adj α (g⁻¹ • γ) := by
    have := (F.adj_smul g⁻¹ α γ).2 hγ
    rwa [show g⁻¹ • α = α by rw [inv_smul_eq_iff]; exact (MulAction.mem_stabilizer_iff.1 hg).symm]
      at this
  rw [← smul_inv_smul g γ, F.mem_nbrStab_smul_iff]
  rw [show g⁻¹ * (g * h * g⁻¹) * g = h by group]
  exact hh.2 _ hγ'

theorem mem_normalizer_ballStab_two {α : V} {g : G} (hg : g ∈ MulAction.stabilizer G α) :
    g ∈ Subgroup.normalizer (ballStab Γ G 2 α : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => F.conj_mem_ballStab_two hg hh, fun hh => ?_⟩
  have := F.conj_mem_ballStab_two (inv_mem hg) hh
  simpa [mul_assoc] using this

theorem mem_normalizer_nbrStab {v : V} {g : G} (hg : g ∈ MulAction.stabilizer G v) :
    g ∈ Subgroup.normalizer (nbrStab Γ G v : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => F.conj_mem_nbrStab_of_stab hg hh, fun hh => ?_⟩
  have := F.conj_mem_nbrStab_of_stab (inv_mem hg) hh
  simpa [mul_assoc] using this

theorem normal_ballStab_two (α : V) :
    ((ballStab Γ G 2 α).subgroupOf (MulAction.stabilizer G α)).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact F.conj_mem_ballStab_two g.2 hn

theorem nbrStab_eq_ballStab_two_of_le {α β : V} (hαβ : Γ.Adj α β)
    (h : nbrStab Γ G α ≤ nbrStab Γ G β) : nbrStab Γ G α = ballStab Γ G 2 α := by
  refine le_antisymm (fun g hg => ?_) fun g hg => ((F.mem_ballStab_two_iff).1 hg).1
  rw [F.mem_ballStab_two_iff]
  refine ⟨hg, fun γ hγ => ?_⟩
  obtain ⟨k, hk, hkβ⟩ := F.loc_trans α β γ hαβ hγ
  have hk' : k ∈ MulAction.stabilizer G α := hk
  have : k⁻¹ * g * k ∈ nbrStab Γ G β := h (by
    have := F.conj_mem_nbrStab_of_stab (inv_mem hk') hg
    simpa using this)
  have h2 := (F.mem_nbrStab_smul_iff k β (h := g)).2 this
  rwa [hkβ] at h2

end FanTree

end CFSG.Quasithin.Fan86

module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3Ab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace Sec8P3

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V}

theorem zGroup_le_stabilizer (h71c : Fan71c F L) : L.zGroup 2 α ≤ MulAction.stabilizer G α := by
  rw [ZLab.zGroup, Subgroup.closure_le]
  rintro g ⟨δ, hd, hδ, rfl⟩
  exact (h71c.z_mem_stabilizer_iff hδ α).2 (by rw [dist_comm]; omega)

theorem zGroup_normal (F : FanTree Γ G) {g : G} (hg : g ∈ MulAction.stabilizer G α) :
    ∀ n ∈ L.zGroup 2 α, g * n * g⁻¹ ∈ L.zGroup 2 α := by
  intro n hn
  rw [ZLab.zGroup] at hn ⊢
  refine Subgroup.closure_induction (p := fun n _ => g * n * g⁻¹ ∈ Subgroup.closure (L.zSet 2 α))
    ?_ ?_ ?_ ?_ hn
  · rintro s ⟨δ, hd, hδ, rfl⟩
    rw [← (L.equivariant g δ hδ)]
    refine Subgroup.subset_closure ⟨g • δ, ?_, by rw [valence_smul F]; exact hδ, rfl⟩
    have := dist_smul F g α δ
    rw [MulAction.mem_stabilizer_iff.1 hg] at this
    rw [this]
    exact hd
  · simp
  · intro a b _ _ iha ihb
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact mul_mem iha ihb
  · intro a _ iha
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem iha

theorem zSet_fcomm (h71c : Fan71c F L) {s t : G} (hs : s ∈ L.zSet 2 α) (ht : t ∈ L.zSet 2 α) :
    fcomm s t = 1 := by
  obtain ⟨δ, hd, hδ, rfl⟩ := hs
  obtain ⟨δ', hd', hδ', rfl⟩ := ht
  have hdist : Γ.dist δ δ' ≤ 4 := by
    have h1 := F.isTree.connected.dist_triangle (u := δ) (v := α) (w := δ')
    have h2 : Γ.dist δ α = Γ.dist α δ := SimpleGraph.dist_comm
    omega
  have hc := h71c.z_comm_of_dist_le hδ hδ' hdist
  calc fcomm (L.z δ) (L.z δ') = (L.z δ * L.z δ') * (L.z δ * L.z δ') := by
        unfold fcomm
        rw [L.z_inv hδ, L.z_inv hδ']
        group
    _ = (L.z δ * L.z δ') * (L.z δ' * L.z δ) := by rw [← hc]
    _ = L.z δ * (L.z δ' * L.z δ') * L.z δ := by group
    _ = 1 := by rw [L.z_mul_self hδ', mul_one, L.z_mul_self hδ]

theorem zGroup_fcomm (h71c : Fan71c F L) :
    ∀ a ∈ L.zGroup 2 α, ∀ b ∈ L.zGroup 2 α, fcomm a b = 1 := by
  intro a ha b hb
  exact Subgroup.mem_bot.1 (fcomm_mem_of_gens ⊥ (L.zSet 2 α) (bot_normalized _)
    (fun s hs t ht => Subgroup.mem_bot.2 (zSet_fcomm h71c hs ht)) a ha b hb)

theorem zGroup_mul_self (h71c : Fan71c F L) : ∀ a ∈ L.zGroup 2 α, a * a = 1 := by
  intro a ha
  refine Subgroup.mem_bot.1 (mul_self_mem_of_gens ⊥ (L.zSet 2 α) (bot_normalized _) ?_ ?_ a ha)
  · intro a ha b hb
    exact Subgroup.mem_bot.2 (zGroup_fcomm h71c a ha b hb)
  · rintro s ⟨δ, -, hδ, rfl⟩
    exact Subgroup.mem_bot.2 (L.z_mul_self hδ)

theorem fcomm_mem_of_right_mem (F : FanTree Γ G) {a : G} (ha : a ∈ MulAction.stabilizer G α)
    {v : G} (hv : v ∈ L.zGroup 2 α) : fcomm a v ∈ L.zGroup 2 α := by
  have h1 : fcomm a v = (a⁻¹ * v⁻¹ * a⁻¹⁻¹) * v := by
    unfold fcomm
    group
  rw [h1]
  exact mul_mem (zGroup_normal F (inv_mem ha) _ (inv_mem hv)) hv

theorem fcomm_mem_of_left_mem (F : FanTree Γ G) {a : G} (ha : a ∈ MulAction.stabilizer G α)
    {v : G} (hv : v ∈ L.zGroup 2 α) : fcomm v a ∈ L.zGroup 2 α := by
  have h1 : fcomm v a = v⁻¹ * (a⁻¹ * v * a⁻¹⁻¹) := by
    unfold fcomm
    group
  rw [h1]
  exact mul_mem (inv_mem hv) (zGroup_normal F (inv_mem ha) _ hv)

end Sec8P3

end CFSG.Quasithin.Fan86

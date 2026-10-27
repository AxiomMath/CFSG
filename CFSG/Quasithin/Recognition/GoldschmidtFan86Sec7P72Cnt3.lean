module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Cnt2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Asm3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace P72

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem exists_smul_of_dist_le (F : FanTree Γ G) {α δ : V} (hα : valence Γ α = 5)
    (hd : Γ.dist α δ ≤ 2) (hδ : valence Γ δ = 5) : ∃ g : G, g • α = δ := by
  have hd' : Γ.dist α δ = 0 ∨ Γ.dist α δ = 1 ∨ Γ.dist α δ = 2 := by omega
  rcases hd' with h0 | h1 | h2
  · exact ⟨1, by
      rw [one_smul]
      exact ((F.isTree.connected.preconnected α δ).dist_eq_zero_iff).1 h0⟩
  · have := valence_adj_three F hα (dist_eq_one_iff_adj.mp h1)
    omega
  · obtain ⟨p, hp⟩ := F.isTree.connected.exists_walk_length_eq_dist α δ
    exact F.exists_smul_of_walk_even 1 p (by omega)

theorem zSet_eq_zBall (F : FanTree Γ G) {α : V} (hα : valence Γ α = 5) :
    L.zSet 2 α = zBall Γ α (L.z α) 2 := by
  ext w
  constructor
  · rintro ⟨δ, hd, hv, rfl⟩
    obtain ⟨g, hg⟩ := exists_smul_of_dist_le F hα hd hv
    refine ⟨g, by rw [hg]; exact hd, ?_⟩
    rw [← hg]
    exact L.equivariant g α hα
  · rintro ⟨g, hd, rfl⟩
    exact ⟨g • α, hd, by rw [valence_smul F]; exact hα, (L.equivariant g α hα).symm⟩

theorem zGroup_card_ge (F : FanTree Γ G) (h40 : Fan40 F) (h64 : Fan64 F) {α : V}
    (hα : valence Γ α = 5) (hfin : Finite ↥(L.zGroup 2 α)) : 2 ^ 5 ≤ Nat.card ↥(L.zGroup 2 α) := by
  have hc := L.isCentral α hα
  have hcin : L.z α ∈ Cinv G α := ⟨hc.2.1, hc.2.2.1, hc.1, hc.2.2.2⟩
  obtain ⟨-, -, hidx⟩ := h64 h40 α (L.z α) hcin
  obtain ⟨x, hx, hxo⟩ := F.exists_orderOf_eq_valence α
  have hV : Subgroup.closure (zBall Γ α (L.z α) 2) = L.zGroup 2 α := by
    rw [← zSet_eq_zBall F hα]
    rfl
  have hidx' := hidx x hx hxo
  rw [hV] at hidx'
  have hzV : L.z α ∈ L.zGroup 2 α := z_mem_zGroup (by rw [SimpleGraph.dist_self]; omega) hα
  have hzC : L.z α ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hc.2.2.2 x hx
  set C := Subgroup.centralizer ({x} : Set G)
  have hmem : (⟨L.z α, hzV⟩ : ↥(L.zGroup 2 α)) ∈ C.subgroupOf (L.zGroup 2 α) :=
    Subgroup.mem_subgroupOf.2 hzC
  have hne : C.subgroupOf (L.zGroup 2 α) ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨L.z α, hzV⟩, hmem⟩, ?_⟩
    intro e
    exact L.z_ne_one hα (congrArg (fun a : ↥(C.subgroupOf (L.zGroup 2 α)) =>
      ((a : ↥(L.zGroup 2 α)) : G)) e)
  have h2 := (Subgroup.one_lt_card_iff_ne_bot (C.subgroupOf (L.zGroup 2 α))).2 hne
  have h3 := Subgroup.card_mul_index (C.subgroupOf (L.zGroup 2 α))
  have h4 : (C.subgroupOf (L.zGroup 2 α)).index = 2 ^ 4 := hidx'
  rw [h4] at h3
  omega

theorem fan72b_of (h : Fan71c F L) (hlab : Lab3 F L) (h40 : Fan40 F) (h64 : Fan64 F) :
    Fan72b F L := by
  intro α hα
  obtain ⟨hfin, hle⟩ := zGroup_card_le h hlab hα
  exact le_antisymm hle (zGroup_card_ge F h40 h64 hα hfin)

end P72

theorem fan_7_2 {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {F : FanTree Γ G}
    {L : ZLab Γ G} (h : Fan71c F L) (hlab : P72.Lab3 F L) (h40 : Fan40 F) (h64 : Fan64 F) :
    Fan72a F L ∧ Fan72b F L :=
  ⟨P72.fan72a_of h hlab, P72.fan72b_of h hlab h40 h64⟩

end CFSG.Quasithin.Fan86

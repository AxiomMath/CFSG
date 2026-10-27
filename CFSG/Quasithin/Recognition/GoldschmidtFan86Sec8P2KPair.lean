module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2KLoc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Aff
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExD10
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P2K

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

structure ExtCfg (D : D10Set L α) (μ ν : V) : Prop where
  adj1 : Γ.Adj (D.delta 0) μ
  ne1 : μ ≠ D.xi 0
  adj2 : Γ.Adj μ ν
  ne2 : ν ≠ D.delta 0

variable {D}

theorem exists_extCfg (F : FanTree Γ G) : ∃ μ ν, ExtCfg D μ ν := by
  obtain ⟨μ, hμ, hμξ⟩ := F.exists_adj_ne (D.delta 0) (D.xi 0)
  obtain ⟨ν, hν, hνδ⟩ := F.exists_adj_ne μ (D.delta 0)
  exact ⟨μ, ν, hμ, hμξ, hν, hνδ⟩

theorem dists_nu (F : FanTree Γ G) {μ ν : V} (hc : ExtCfg D μ ν) :
    Γ.dist ν (D.delta 0) = 2 ∧ Γ.dist ν (D.xi 0) = 3 ∧ Γ.dist ν (D.alpha 0) = 4 ∧
      Γ.dist ν (D.beta 0) = 5 ∧ Γ.dist ν α = 6 := by
  have d1 : Γ.dist ν μ = 1 := dist_eq_one_iff_adj.2 hc.adj2.symm
  have d2 : Γ.dist ν (D.delta 0) = 2 :=
    IsTree.dist_eq_two_of_adj F.isTree hc.adj2.symm hc.adj1.symm hc.ne2.symm
  have d3 : Γ.dist ν (D.xi 0) = Γ.dist ν (D.delta 0) + 1 :=
    IsTree.dist_succ_of_ne F.isTree hc.adj1 (D.adj_xi_delta 0).symm hc.ne1 (by omega)
  have d4 : Γ.dist ν (D.alpha 0) = Γ.dist ν (D.xi 0) + 1 :=
    IsTree.dist_succ_of_ne F.isTree (D.adj_xi_delta 0) (D.adj_alpha_xi 0).symm
      (D.delta_ne_alpha 0) (by omega)
  have d5 : Γ.dist ν (D.beta 0) = Γ.dist ν (D.alpha 0) + 1 :=
    IsTree.dist_succ_of_ne F.isTree (D.adj_alpha_xi 0) (D.adj_beta_alpha 0).symm
      (D.xi_ne_beta 0) (by omega)
  have d6 : Γ.dist ν α = Γ.dist ν (D.beta 0) + 1 :=
    IsTree.dist_succ_of_ne F.isTree (D.adj_beta_alpha 0) (D.adj_start_beta 0).symm
      (D.alpha_ne_start 0) (by omega)
  refine ⟨d2, by omega, by omega, by omega, by omega⟩

theorem valence_nu (F : FanTree Γ G) {μ ν : V} (hc : ExtCfg D μ ν) : valence Γ ν = 5 := by
  have h := (dists_nu F hc).1
  have h' : Γ.dist (D.delta 0) ν = 2 := by rw [SimpleGraph.dist_comm]; exact h
  exact valence_of_dist_even F (D.valence_delta F 0) (by rw [h'])

theorem calpha_ne_zpowers (h4 : Nat.card ↥D.calpha = 4) : D.calpha ≠ Subgroup.zpowers (L.z α) := by
  intro h
  have hz2 : Nat.card ↥(Subgroup.zpowers (L.z α)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using L.z_mul_self D.val) (L.z_ne_one D.val)
  have h' : Nat.card ↥D.calpha = Nat.card ↥(Subgroup.zpowers (L.z α)) := by rw [h]
  omega

theorem isZ2Pair_alpha' (F : FanTree Γ G) (h7 : Fan7 F L) {μ ν : V} (hc : ExtCfg D μ ν) :
    IsZ2Pair Γ G α (D.alpha 0) (D.beta 0) (D.delta 0) (L.z ν • α) 2 := by
  have h71c : Fan71c F L := h7.2.2.1
  have hvν := valence_nu F hc
  obtain ⟨-, d3, d4, d5, d6⟩ := dists_nu F hc
  have hs2 : L.z ν * L.z ν = 1 := L.z_mul_self hvν
  have hsa6 : L.z ν • D.alpha 0 = D.alpha 0 := (h71c.z_smul_eq_iff hvν _).2 (by omega)
  have hsξ : L.z ν • D.xi 0 = D.xi 0 := (h71c.z_smul_eq_iff hvν _).2 (by omega)
  have hsβ : L.z ν • D.beta 0 ≠ D.beta 0 := fun h => by
    have := (h71c.z_smul_eq_iff hvν _).1 h
    omega
  have hsα : L.z ν • α ≠ D.alpha 0 := by
    intro h
    have h' : L.z ν • α = L.z ν • D.alpha 0 := h.trans hsa6.symm
    exact D.alpha_ne_start 0 (MulAction.injective _ h').symm
  have hadjβα : Γ.Adj (L.z ν • D.beta 0) (L.z ν • α) :=
    (F.adj_smul _ _ _).2 (D.adj_start_beta 0).symm
  refine ⟨D.dist_start_alpha F 0, (D.adj_beta_alpha 0).symm,
    by rw [D.dist_start_beta F 0, D.dist_start_alpha F 0], D.dist_alpha_delta F 0, ?_,
    by rw [D.dist_delta F 0], ?_, ?_⟩
  · have := dist_smul F (L.z ν) (D.alpha 0) α
    rw [hsa6] at this
    rw [this, D.dist_alpha_start F 0]
  · refine IsTree.dist_eq_four_of_branches F.isTree (D.adj_beta_alpha 0).symm
      (D.adj_start_beta 0).symm ?_ hadjβα (fun h => hsβ h.symm) (D.alpha_ne_start 0).symm hsα
    have := (F.adj_smul (L.z ν) (D.alpha 0) (D.beta 0)).2 (D.adj_beta_alpha 0).symm
    rwa [hsa6] at this
  · obtain ⟨D'⟩ := exists_d10Set h7 (D.valence_alpha F 0)
    have hx' : D'.x⁻¹ ∈ MulAction.stabilizer G (D.alpha 0) := inv_mem (D'.x_mem_stabilizer F h71c)
    obtain ⟨j, hj⟩ := D'.exists_beta_eq F h71c (D.adj_beta_alpha 0).symm
    obtain ⟨p, hp⟩ := D'.exists_beta_eq F h71c (D.adj_alpha_xi 0)
    have hpj : p ≠ j := fun h => D.xi_ne_beta 0 (by rw [← hp, ← hj, h])
    have hsK : L.z ν ∉ nbrStab Γ G (D.alpha 0) := fun h =>
      hsβ (mem_nbrStab.1 h _ (D.adj_beta_alpha 0).symm)
    have hsa_mem : L.z ν ∈ MulAction.stabilizer G (D.alpha 0) :=
      MulAction.mem_stabilizer_iff.2 hsa6
    have hsp : L.z ν • D'.beta p = D'.beta p := by
      rw [hp]
      exact hsξ
    have key := F.smul_eq_two_mul_sub D'.val hx' D'.adj_start_beta (D'.beta_injective F h71c)
      (D'.hxβ F h71c) hsa_mem hsp hs2 hsK j
    have hq : ∀ p j : Fin 5, p ≠ j →
        (2 * p - j) - j ≠ p - j ∧ (2 * p - j) - j ≠ -(p - j) := by decide
    have := F.not_exists_gcirc_of_affine D'.val hx' D'.adj_start_beta
      (D'.beta_injective F h71c) (D'.hxβ F h71c) j p (2 * p - j)
      (δ := D.delta 0) (δ' := L.z ν • α)
      (by rw [hp]; exact D.adj_xi_delta 0) (by rw [← key, hj]; exact hadjβα) hsα (hq p j hpj)
    rwa [hj] at this

theorem kleinU_moves_alpha' (F : FanTree Γ G) (h7 : Fan7 F L) (h83c : Fan83c F L) {μ ν : V}
    {u : G} (hu : KleinU D u) (h4 : Nat.card ↥D.calpha = 4) (hc : ExtCfg D μ ν) :
    u • (L.z ν • α) ≠ L.z ν • α := by
  intro hfix
  have h71c : Fan71c F L := h7.2.2.1
  have h75 : Fan75 F L := h7.2.2.2.2.2.2.2.2
  have hpair := isZ2Pair_alpha' F h7 hc
  have hcl := h83c α D (calpha_ne_zpowers h4) 0 _ _ hpair
  have hδ5 := D.valence_delta F 0
  have hα'5 : valence Γ (L.z ν • α) = 5 := by
    rw [valence_smul F]
    exact D.val
  have hzδ : L.z α • D.delta 0 = D.delta 0 := by
    rw [h71c.z_smul_eq_iff D.val, D.dist_delta F 0]
  have hzα' : L.z α • (L.z ν • α) = L.z ν • α := by
    rw [h71c.z_smul_eq_iff D.val]
    have := hpair.2.2.2.2.2.2.1
    omega
  have huδ : u • D.delta 0 = D.delta 0 :=
    MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hu.fix0)
  set y := L.z (D.delta 0) * L.z (L.z ν • α) with hy
  have hcz1 : Commute (L.z α) (L.z (D.delta 0)) := (h71c.comm_z_iff hδ5 (L.z α)).2 hzδ
  have hcz2 : Commute (L.z α) (L.z (L.z ν • α)) := (h71c.comm_z_iff hα'5 (L.z α)).2 hzα'
  have hcu1 : Commute u (L.z (D.delta 0)) := (h71c.comm_z_iff hδ5 u).2 huδ
  have hcu2 : Commute u (L.z (L.z ν • α)) := (h71c.comm_z_iff hα'5 u).2 hfix
  have hcz : Commute (L.z α) y := hcz1.mul_right hcz2
  have hcu : Commute u y := hcu1.mul_right hcu2
  have hall : ∀ c ∈ D.calpha, fcomm y c = 1 := by
    intro c hc'
    have hcy : Commute c y := by
      rcases klein_cases F h71c h75 hu h4 c hc' with h | h | h | h
      · rw [h]
        exact Commute.one_left _
      · rw [h]
        exact hcz
      · rw [h]
        exact hcu
      · rw [h]
        exact hcu.mul_left hcz
    have h1 : y * c = c * y := hcy.symm.eq
    calc fcomm y c = (c * y)⁻¹ * (y * c) := by
          unfold fcomm
          group
      _ = 1 := by rw [h1]; exact inv_mul_cancel _
  have hle : Subgroup.closure {g | ∃ c ∈ D.calpha, g = fcomm y c} ≤ ⊥ := by
    rw [Subgroup.closure_le]
    rintro g ⟨c, hc', rfl⟩
    rw [hall c hc']
    exact one_mem _
  rw [hcl] at hle
  have hz : L.z (D.alpha 0) ∈ (⊥ : Subgroup G) := hle (Subgroup.mem_zpowers _)
  exact L.z_ne_one (D.valence_alpha F 0) (Subgroup.mem_bot.1 hz)

end Sec8P2K

end CFSG.Quasithin.Fan86

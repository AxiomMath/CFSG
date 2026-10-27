module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2KPair
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2KBall
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Key

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P2K

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem false_of_klein (F : FanTree Γ G) (h7 : Fan7 F L) (h83c : Fan83c F L)
    (hk : ∀ c ∈ D.calpha, c * c = 1) (h4 : Nat.card ↥D.calpha = 4) : False := by
  have h71a : Fan71a F L := h7.1
  have h71c : Fan71c F L := h7.2.2.1
  have h75 : Fan75 F L := h7.2.2.2.2.2.2.2.2
  obtain ⟨u, hu⟩ := exists_kleinU D F h71a h71c h75 hk h4
  obtain ⟨μ, ν, hc⟩ := exists_extCfg (D := D) F
  have hvν := valence_nu F hc
  have hmove := kleinU_moves_alpha' F h7 h83c hu h4 hc
  have huμ : u • μ = μ := mem_nbrStab.1 hu.fix0 μ hc.adj1
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu.sq
  have hs2 : L.z ν * L.z ν = 1 := L.z_mul_self hvν
  have hν' : valence Γ (u • ν) = 5 := by
    rw [valence_smul F]
    exact hvν
  have hdist : Γ.dist (u • ν) ν ≤ 4 := by
    have h1 : Γ.Adj (u • μ) (u • ν) := (F.adj_smul u μ ν).2 hc.adj2
    rw [huμ] at h1
    have := F.isTree.connected.dist_triangle (u := u • ν) (v := μ) (w := ν)
    rw [dist_eq_one_iff_adj.2 h1.symm, dist_eq_one_iff_adj.2 hc.adj2] at this
    omega
  have hcz := h71c.z_comm_of_dist_le hν' hvν hdist
  rw [L.equivariant u ν hvν, huinv] at hcz
  have hcomm : u * (L.z ν * u * L.z ν) = (L.z ν * u * L.z ν) * u := by
    calc u * (L.z ν * u * L.z ν) = (u * L.z ν * u) * L.z ν := by group
      _ = L.z ν * (u * L.z ν * u) := hcz
      _ = (L.z ν * u * L.z ν) * u := by group
  have hsa0 : L.z ν • D.alpha 0 = D.alpha 0 :=
    (h71c.z_smul_eq_iff hvν _).2 (by have := (dists_nu F hc).2.2.1; omega)
  have hu''K : L.z ν * u * L.z ν ∈ nbrStab Γ G (D.alpha 0) :=
    conj_mem_nbrStab F hsa0 hs2 (hu.mem_nbrStab_alpha F h71a h71c 0)
  have hu''β : (L.z ν * u * L.z ν) • D.beta 0 = D.beta 0 :=
    mem_nbrStab.1 hu''K _ (D.adj_beta_alpha 0).symm
  have hu''α : (L.z ν * u * L.z ν) • α ≠ α := by
    intro h
    apply hmove
    have h1 : L.z ν • (u • (L.z ν • α)) = α := by simpa [mul_smul] using h
    calc u • (L.z ν • α) = (L.z ν * L.z ν) • (u • (L.z ν • α)) := by rw [hs2, one_smul]
      _ = L.z ν • (L.z ν • (u • (L.z ν • α))) := by rw [mul_smul]
      _ = L.z ν • α := by rw [h1]
  have huα : u • α = α :=
    MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α hu.mem_nbrStab)
  have huα0 : u • D.alpha 0 = D.alpha 0 :=
    D.fix_of_mem_calpha F h71a h71c hu.mem 0 (m := 2) (by norm_num)
  have htβ : Γ.Adj (D.beta 0) ((L.z ν * u * L.z ν) • α) := by
    have := (F.adj_smul (L.z ν * u * L.z ν) (D.beta 0) α).2 (D.adj_start_beta 0).symm
    rwa [hu''β] at this
  have hKt : u ∈ nbrStab Γ G ((L.z ν * u * L.z ν) • α) := by
    rw [mem_nbrStab]
    intro w hw
    have hw0 : Γ.Adj α ((L.z ν * u * L.z ν)⁻¹ • w) := by
      have := (F.adj_smul (L.z ν * u * L.z ν)⁻¹ _ w).2 hw
      rwa [inv_smul_smul] at this
    have huw0 := mem_nbrStab.1 hu.mem_nbrStab _ hw0
    calc u • w = u • ((L.z ν * u * L.z ν) • ((L.z ν * u * L.z ν)⁻¹ • w)) := by
          rw [smul_inv_smul]
      _ = (L.z ν * u * L.z ν) • (u • ((L.z ν * u * L.z ν)⁻¹ • w)) := by
          rw [← mul_smul, hcomm, mul_smul]
      _ = (L.z ν * u * L.z ν) • ((L.z ν * u * L.z ν)⁻¹ • w) := by rw [huw0]
      _ = w := smul_inv_smul _ _
  have hKβ : u ∈ nbrStab Γ G (D.beta 0) :=
    F.fix_two_nbrs (D.adj_start_beta 0).symm (D.adj_beta_alpha 0) (D.alpha_ne_start 0).symm huα
      huα0
  have hnbrs : ∀ n, Γ.Adj (D.beta 0) n →
      n = α ∨ n = D.alpha 0 ∨ n = (L.z ν * u * L.z ν) • α := by
    intro n hn
    obtain ⟨c, hcs, hac, hbc⟩ := exists_third_neighbor (D.valence_beta F 0)
      (D.adj_start_beta 0).symm (D.adj_beta_alpha 0) (D.alpha_ne_start 0).symm
    have hn' : n ∈ Γ.neighborSet (D.beta 0) := hn
    have ht' : (L.z ν * u * L.z ν) • α ∈ Γ.neighborSet (D.beta 0) := htβ
    rw [hcs] at hn' ht'
    have htα : (L.z ν * u * L.z ν) • α ≠ D.alpha 0 := by
      intro h
      have h' : (L.z ν * u * L.z ν) • α = (L.z ν * u * L.z ν) • D.alpha 0 := by
        rw [h]
        exact (MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hu''K)).symm
      exact D.alpha_ne_start 0 (MulAction.injective _ h').symm
    have htα' : (L.z ν * u * L.z ν) • α ≠ α := hu''α
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn' ht'
    rcases ht' with h | h | h
    · exact absurd h htα'
    · exact absurd h htα
    · rcases hn' with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (h'.trans h.symm))
  have hnbrK : ∀ n, Γ.Adj (D.beta 0) n → u ∈ nbrStab Γ G n := by
    intro n hn
    rcases hnbrs n hn with h | h | h
    · rw [h]
      exact hu.mem_nbrStab
    · rw [h]
      exact hu.mem_nbrStab_alpha F h71a h71c 0
    · rw [h]
      exact hKt
  have hball : u ∈ ballStab Γ G 2 (D.beta 0) := by
    rw [mem_ballStab]
    intro v hv
    rcases Nat.lt_or_ge (Γ.dist (D.beta 0) v) 2 with h | h
    · rcases Nat.lt_or_ge (Γ.dist (D.beta 0) v) 1 with h0 | h1
      · have : v = D.beta 0 := by
          have h0' : Γ.dist (D.beta 0) v = 0 := by omega
          exact ((SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0').resolve_right
            (not_not.2 (F.isTree.connected.preconnected _ _))).symm
        rw [this]
        exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hKβ)
      · have h1' : Γ.dist (D.beta 0) v = 1 := by omega
        exact mem_nbrStab.1 hKβ v (dist_eq_one_iff_adj.1 h1')
    · obtain ⟨c, h1, h2⟩ := exists_adj_adj_of_dist_two F.isTree (a := D.beta 0) (δ := v)
        (by omega)
      exact mem_nbrStab.1 (hnbrK c h1) v h2
  have hball_all : ∀ j : Fin 5, u ∈ ballStab Γ G 2 (D.beta j) := by
    intro j
    rw [← x_pow_inv_smul_beta D F h71c j, mem_ballStab_smul_iff F]
    have h1 := calpha_comm_x_pow D hu.mem j.val
    have e : ((D.x ^ j.val)⁻¹)⁻¹ * u * (D.x ^ j.val)⁻¹ = u := by
      rw [inv_inv, ← h1]
      group
    rw [e]
    exact hball
  have hball3 : u ∈ ballStab Γ G 3 α := by
    rw [mem_ballStab]
    intro v hv
    by_cases hva : v = α
    · rw [hva]
      exact huα
    · obtain ⟨b, hb, hbv⟩ := exists_nbr_dist_le F (n := 2) hv hva
      obtain ⟨j, rfl⟩ := D.exists_beta_eq F h71c hb
      exact mem_ballStab.1 (hball_all j) v hbv
  obtain ⟨P, -, h4', -, -, -, -, -⟩ := exists_arc8_calpha D F h71a h71c
  have hv : valence Γ (P.vert 4) = 5 := by
    rw [h4']
    exact D.val
  have hz := (h75 P hv).1
  rw [h4'] at hz
  rw [hz] at hball3
  exact hu.not_mem hball3

end Sec8P2K

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_4a (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h83c : Fan83c F L) :
    Fan84a F L := by
  intro α D
  have h71a : Fan71a F L := h7.1
  have h71c : Fan71c F L := h7.2.2.1
  have h75 : Fan75 F L := h7.2.2.2.2.2.2.2.2
  have hle := Sec8P2K.card_calpha_le_four D F h71a h71c h75
  by_cases hcyc : IsCyclic ↥D.calpha
  · exact ⟨hcyc, hle⟩
  · exfalso
    obtain ⟨h4, hk⟩ := Sec8P2K.klein_of_not_cyclic D F h71a h71c h75 hcyc
    exact Sec8P2K.false_of_klein D F h7 h83c hk h4

end CFSG.Quasithin.Fan86

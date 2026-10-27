module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt1
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Dist
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Refl
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L) {F : FanTree Γ G}

theorem xβ_pow_three : S.xβ ^ 3 = 1 := by
  rw [← S.isBeta.order3]; exact pow_orderOf_eq_one _

theorem xβ_smul_beta : S.xβ • S.beta = S.beta := S.isBeta.fixβ

theorem t_eq : S.t = L.z (S.D.delta 0) * L.z S.η' := by
  simp [Sec9Cfg.t, D10Set.y]

theorem valence_etaP (F : FanTree Γ G) : valence Γ S.η' = 5 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := S.isBeta.pair
  exact valence_of_dist_even F S.D.val (by rw [h7])

theorem dist_delta_etaP (F : FanTree Γ G) : Γ.dist (S.D.delta 0) S.η' ≤ 4 := by
  obtain ⟨-, -, -, -, h5, -⟩ := S.isBeta.pair
  have h := F.isTree.connected.dist_triangle (u := S.D.delta 0) (v := S.D.alpha 0) (w := S.η')
  have e : Γ.dist (S.D.delta 0) (S.D.alpha 0) = 2 := by
    rw [SimpleGraph.dist_comm]; exact S.D.dist_alpha_delta F 0
  omega

theorem t_sq {F : FanTree Γ G} (h71c : Fan71c F L) : S.t * S.t = 1 := by
  rw [S.t_eq]
  have hc := h71c.z_comm_of_dist_le (S.D.valence_delta F 0) (S.valence_etaP F)
    (S.dist_delta_etaP F)
  have h0 := S.D.zd_mul_self F 0
  have h1 := L.z_mul_self (S.valence_etaP F)
  calc L.z (S.D.delta 0) * L.z S.η' * (L.z (S.D.delta 0) * L.z S.η')
      = L.z (S.D.delta 0) * (L.z S.η' * L.z (S.D.delta 0)) * L.z S.η' := by group
    _ = (L.z (S.D.delta 0) * L.z (S.D.delta 0)) * (L.z S.η' * L.z S.η') := by
        rw [← hc]; group
    _ = 1 := by rw [h0, h1, mul_one]

theorem t_inv {F : FanTree Γ G} (h71c : Fan71c F L) : S.t⁻¹ = S.t :=
  inv_eq_of_mul_eq_one_right (S.t_sq h71c)

theorem t_conj_xβ {F : FanTree Γ G} (h71c : Fan71c F L) : S.t * S.xβ * S.t = S.xβ⁻¹ := by
  have h : S.t⁻¹ * S.xβ * S.t = S.xβ⁻¹ := S.isBeta.inverts
  rwa [S.t_inv h71c] at h

theorem t_mul_xβ_pow_inv {F : FanTree Γ G} (h71c : Fan71c F L) (k : ℕ) :
    S.t * (S.xβ ^ k)⁻¹ = S.xβ ^ k * S.t := by
  have h1 : S.t * S.xβ * S.t⁻¹ = S.xβ⁻¹ := by rw [S.t_inv h71c]; exact S.t_conj_xβ h71c
  have h1' : S.t * S.xβ⁻¹ * S.t⁻¹ = S.xβ := by
    have := congrArg (fun y => y⁻¹) h1
    simpa [mul_assoc] using this
  have h2 : S.t * (S.xβ ^ k)⁻¹ * S.t⁻¹ = S.xβ ^ k := by
    rw [← inv_pow, ← conj_pow, h1']
  calc S.t * (S.xβ ^ k)⁻¹ = (S.t * (S.xβ ^ k)⁻¹ * S.t⁻¹) * S.t := by group
    _ = S.xβ ^ k * S.t := by rw [h2]

theorem t_smul_inv_pow_smul {F : FanTree Γ G} (h71c : Fan71c F L) (k : ℕ) (v : V) :
    S.t • ((S.xβ ^ k)⁻¹ • v) = S.xβ ^ k • (S.t • v) := by
  rw [← mul_smul, S.t_mul_xβ_pow_inv h71c, mul_smul]

theorem t_smul_eq {F : FanTree Γ G} (h81 : Fan81 F L) {v : V}
    (hv2 : Γ.dist (S.D.alpha 0) v ≤ 2 ∨ Γ.dist (S.D.beta 0) v ≤ 2) : S.t • v = v := by
  have h := h81 S.α (S.D.alpha 0) (S.D.beta 0) (S.D.delta 0) S.η' S.D.val S.isBeta.pair
  have hmem : v ∈ {v | Γ.dist S.α v ≤ 4 ∧ (L.z (S.D.delta 0) * L.z S.η') • v = v} := by
    rw [h]; exact hv2
  rw [S.t_eq]
  exact hmem.2

theorem t_smul_alpha0 {F : FanTree Γ G} (h81 : Fan81 F L) : S.t • S.D.alpha 0 = S.D.alpha 0 :=
  S.t_smul_eq h81 (Or.inl (by simp))

theorem collar_one : (S.xβ ^ 2)⁻¹ • S.α = S.D.alpha 2 := by
  have h := S.isBeta.collar 1 (by norm_num)
  simp [D10Set.bv, S.D.start 0] at h
  exact h

theorem collar_three : (S.xβ ^ 2)⁻¹ • S.D.alpha 0 = S.D.delta 2 := by
  have h := S.isBeta.collar 3 (by norm_num)
  simp [D10Set.bv] at h
  exact h

theorem xβ_inv_smul_delta2 : S.xβ⁻¹ • S.D.delta 2 = S.D.alpha 0 := by
  rw [← S.collar_three, ← mul_smul]
  have h3 := S.xβ_pow_three
  have h4 : S.xβ ^ 2 * S.xβ = 1 := by rw [← pow_succ]; exact h3
  have : S.xβ⁻¹ * (S.xβ ^ 2)⁻¹ = 1 := by rw [← mul_inv_rev, h4, inv_one]
  rw [this, one_smul]

theorem xβ_pow_two_inv_smul (v : V) : (S.xβ ^ 2)⁻¹ • v = S.xβ⁻¹ • S.xβ⁻¹ • v := by
  rw [pow_two, mul_inv_rev, mul_smul]

theorem xβ_inv_smul_alpha2 : S.xβ⁻¹ • S.D.alpha 2 = S.α := by
  rw [← S.collar_one, ← mul_smul]
  have h4 : S.xβ ^ 2 * S.xβ = 1 := by rw [← pow_succ]; exact S.xβ_pow_three
  have : S.xβ⁻¹ * (S.xβ ^ 2)⁻¹ = 1 := by rw [← mul_inv_rev, h4, inv_one]
  rw [this, one_smul]

theorem xβ_inv_smul_xβ_inv_alpha : S.xβ⁻¹ • S.xβ⁻¹ • S.α = S.D.alpha 2 := by
  rw [← S.xβ_pow_two_inv_smul, S.collar_one]

theorem alpha_ne_xβ_inv : S.xβ⁻¹ • S.α ≠ S.α := by
  intro h
  apply S.D.alpha_ne_start 2
  rw [← S.collar_one, S.xβ_pow_two_inv_smul, h, h]

theorem xβ_inv_alpha_ne_alpha2 : S.xβ⁻¹ • S.α ≠ S.D.alpha 2 := by
  intro h
  apply S.alpha_ne_xβ_inv
  have h1 : S.xβ⁻¹ • S.xβ⁻¹ • S.α = S.D.alpha 2 := S.xβ_inv_smul_xβ_inv_alpha
  rw [← h] at h1
  exact (MulAction.injective S.xβ⁻¹ h1).symm ▸ rfl

theorem neighborSet_beta (F : FanTree Γ G) :
    Γ.neighborSet S.beta = {S.α, S.xβ⁻¹ • S.α, S.D.alpha 2} := by
  have hβ3 : valence Γ S.beta = 3 := S.D.valence_beta F 2
  have hadj1 : Γ.Adj S.beta S.α := (S.D.adj_start_beta 2).symm
  have hadj2 : Γ.Adj S.beta (S.xβ⁻¹ • S.α) := by
    have h := (F.adj_smul S.xβ⁻¹ S.beta S.α).2 hadj1
    have hb : S.xβ⁻¹ • S.beta = S.beta := by
      rw [inv_smul_eq_iff]; exact S.xβ_smul_beta.symm
    rwa [hb] at h
  have hadj3 : Γ.Adj S.beta (S.D.alpha 2) := S.D.adj_beta_alpha 2
  have hne1 : S.α ≠ S.xβ⁻¹ • S.α := fun h => S.alpha_ne_xβ_inv h.symm
  have hne2 : S.α ≠ S.D.alpha 2 := fun h => S.D.alpha_ne_start 2 h.symm
  have hne3 : S.xβ⁻¹ • S.α ≠ S.D.alpha 2 := S.xβ_inv_alpha_ne_alpha2
  have hsub : ({S.α, S.xβ⁻¹ • S.α, S.D.alpha 2} : Set V) ⊆ Γ.neighborSet S.beta := by
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact hadj1
    · exact hadj2
    · exact hadj3
  have hcard : (Γ.neighborSet S.beta).ncard ≤ ({S.α, S.xβ⁻¹ • S.α, S.D.alpha 2} : Set V).ncard := by
    rw [neighborSet_ncard hβ3, Set.ncard_eq_three.2 ⟨_, _, _, hne1, hne2, hne3, rfl⟩]
  exact (Set.eq_of_subset_of_ncard_le hsub hcard (neighborSet_finite (by norm_num) hβ3)).symm

theorem t_smul_delta2 (h71c : Fan71c F L) (h81 : Fan81 F L) :
    S.t • S.D.delta 2 = S.xβ⁻¹ • S.D.alpha 0 := by
  rw [← S.collar_three, S.t_smul_inv_pow_smul h71c 2, S.t_smul_alpha0 h81]
  have h4 : S.xβ ^ 2 * S.xβ = 1 := by rw [← pow_succ]; exact S.xβ_pow_three
  rw [eq_inv_of_mul_eq_one_left h4]

end Sec9Cfg

end CFSG.Quasithin.Fan86

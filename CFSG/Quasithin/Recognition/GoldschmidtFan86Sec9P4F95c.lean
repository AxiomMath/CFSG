module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95Psi
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Z2A
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Coll
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Rel
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F93b

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem isZ2Pair_mu3 (F : FanTree Γ G) (h71c : Fan71c F L) :
    IsZ2Pair Γ G S.α (S.D.alpha 2) (S.D.beta 2) ((S.xβ ^ 2)⁻¹ • S.D.alpha 0)
      ((S.xβ ^ 2)⁻¹ • S.D.alpha 1) 2 := by
  have hβ : ∀ n : ℕ, (S.xβ ^ n) • S.D.beta 2 = S.D.beta 2 := fun n =>
    MulAction.mem_stabilizer_iff.1
      (Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.2 S.xβ_smul_beta) n)
  have hl : Γ.Adj (S.D.beta 2) ((S.xβ ^ 2) • S.α) := by
    have := (F.adj_smul (S.xβ ^ 2) (S.D.beta 2) S.α).2 (S.D.adj_start_beta 2).symm
    rwa [hβ 2] at this
  have hne : (S.xβ ^ 2) • S.α ≠ S.α := fun h' =>
    S.D.alpha_ne_start 2 (by rw [← S.collar_one]; exact inv_smul_eq_iff.2 h'.symm)
  have h := S.D.isZ2Pair_alpha_lam F h71c (i := 2) (j := 0) (k := 1) (by decide) (by decide)
    (by decide) (by decide) hl hne
  have h' := IsZ2Pair.smul F (S.xβ ^ 2)⁻¹ h
  have hβ' : (S.xβ ^ 2)⁻¹ • S.D.beta 2 = S.D.beta 2 := inv_smul_eq_iff.2 (hβ 2).symm
  rwa [inv_smul_smul, S.collar_one, hβ'] at h'

theorem fcomm_yMu_two_t (F : FanTree Γ G) (h71c : Fan71c F L) (h83d : Fan83d F L) :
    ∃ e : Fin 2, fcomm (S.yMu 2) S.t =
      L.z (S.D.alpha 3) * L.z (S.D.alpha 4) * L.z S.α ^ (e : ℕ) := by
  obtain ⟨e, he⟩ := h83d.1 S.α S.D 2 0 (by decide) _ _ _ _ (S.isZ2Pair_mu3 F h71c)
    S.isBeta.pair
  refine ⟨e, ?_⟩
  have e1 : kstar 2 0 = (3 : Fin 5) := by decide
  have e2 : kstar 0 2 = (4 : Fin 5) := by decide
  rw [e1, e2] at he
  rw [S.t_eq]
  exact he

theorem t_psi (F : FanTree Γ G) (h71c : Fan71c F L) (g : G) :
    S.t * (S.xβ⁻¹ * g * S.xβ) * S.t = S.xβ * (S.t * g * S.t) * S.xβ⁻¹ := by
  have ht := S.t_sq h71c
  have h2 := S.t_conj_xβ h71c
  have h1 : S.t * S.xβ⁻¹ * S.t = S.xβ := by
    have := congrArg (fun x => x⁻¹) h2
    simpa [mul_inv_rev, S.t_inv h71c, mul_assoc] using this
  have key : ∀ A B C : G, S.t * (A * B * C) * S.t = (S.t * A * S.t) * (S.t * B * S.t) *
      (S.t * C * S.t) := fun A B C => by
    calc S.t * (A * B * C) * S.t = S.t * A * (S.t * S.t) * B * (S.t * S.t) * C * S.t := by
          rw [ht]; group
      _ = _ := by group
  rw [key, h1, h2]

theorem t_conj_za (F : FanTree Γ G) (h71c : Fan71c F L) : S.t * L.z S.α * S.t = L.z S.α := by
  have hc : S.t * L.z S.α = L.z S.α * S.t :=
    L.comm_z_of_mem_stabilizer S.D.val (S.y_mem_stabilizer F h71c 0)
  rw [hc, mul_assoc, S.t_sq h71c, mul_one]

theorem psi2_zMu1 (F : FanTree Γ G) (j : Fin 5) :
    S.xβ * S.zMu1 j * S.xβ⁻¹ = S.zMuij 2 j := by
  rw [← S.psi_psi, S.psi_zMu1 F, S.psi_zMuij_one F]

theorem psi2_za (F : FanTree Γ G) : S.xβ * L.z S.α * S.xβ⁻¹ = S.zNb 2 := by
  rw [← S.psi_psi, S.psi_zalpha, S.psi_zNb1 F]

theorem t_conj_zNb_one (F : FanTree Γ G) (h71c : Fan71c F L) :
    S.t * S.zNb 1 * S.t = S.zNb 2 := by
  rw [← S.psi_zalpha, S.psi_apply, S.t_psi F h71c, S.t_conj_za F h71c, S.psi2_za F]

theorem t_conj_zNb_two (F : FanTree Γ G) (h71c : Fan71c F L) :
    S.t * S.zNb 2 * S.t = S.zNb 1 := by
  have ht := S.t_sq h71c
  have h := S.t_conj_zNb_one F h71c
  calc S.t * S.zNb 2 * S.t = S.t * (S.t * S.zNb 1 * S.t) * S.t := by rw [h]
    _ = S.zNb 1 := by
      calc S.t * (S.t * S.zNb 1 * S.t) * S.t = (S.t * S.t) * S.zNb 1 * (S.t * S.t) := by group
        _ = S.zNb 1 := by rw [ht]; group

theorem zNb_one_mul_self (F : FanTree Γ G) : S.zNb 1 * S.zNb 1 = 1 := by
  rw [S.zNb_one]
  exact L.z_mul_self ((valence_smul F S.xβ⁻¹ S.α).trans S.D.val)

theorem zNb_one_eq (F : FanTree Γ G) (h71c : Fan71c F L) (h512 : Fan512 F L) :
    S.zNb 1 = L.z S.α * S.zMu1 2 := by
  rw [← S.zalpha_mul_zNb_two F h71c h512, S.zNb_two]
  rfl

theorem yMu_zero_eq_zMu1 : S.yMu 0 = S.zMu1 0 * S.zMu1 1 := by
  show S.zMuij 0 0 * S.zMuij 0 1 = _
  rw [S.zMuij_zero, S.zMuij_zero]

theorem t_conj_yMu_one (F : FanTree Γ G) (h71c : Fan71c F L) (h83b : Fan83b F L) :
    S.t * S.yMu 1 * S.t = S.yMu 2 * S.zNb 2 := by
  have ht := S.t_sq h71c
  have h1 : S.yMu 1 = MulAut.conj S.xβ⁻¹ (S.zMu1 0 * S.zMu1 1) := by
    rw [map_mul, S.psi_zMu1 F, S.psi_zMu1 F]
    rfl
  have e0 := S.t_conj_zMu1_zero h71c h83b
  have e1 := S.t_conj_zMu1_ne h71c h83b (j := 1) (by decide)
  have hY0 : S.t * (S.zMu1 0 * S.zMu1 1) * S.t = S.zMu1 0 * (L.z S.α * S.zMu1 1) := by
    calc S.t * (S.zMu1 0 * S.zMu1 1) * S.t
        = S.t * S.zMu1 0 * (S.t * S.t) * S.zMu1 1 * S.t := by rw [ht]; group
      _ = (S.t * S.zMu1 0 * S.t) * (S.t * S.zMu1 1 * S.t) := by group
      _ = _ := by rw [e0, e1]
  rw [h1, S.psi_apply, S.t_psi F h71c, hY0]
  calc S.xβ * (S.zMu1 0 * (L.z S.α * S.zMu1 1)) * S.xβ⁻¹
      = (S.xβ * S.zMu1 0 * S.xβ⁻¹) * (S.xβ * L.z S.α * S.xβ⁻¹) * (S.xβ * S.zMu1 1 * S.xβ⁻¹) := by
        group
    _ = S.zMuij 2 0 * S.zNb 2 * S.zMuij 2 1 := by
        rw [S.psi2_zMu1 F, S.psi2_zMu1 F, S.psi2_za F]
    _ = S.yMu 2 * S.zNb 2 := by
        rw [mul_assoc, ← (S.zMuij_two_comm_nb F h71c 1).eq, ← mul_assoc]
        rfl

theorem t_conj_yMu_two (F : FanTree Γ G) (h71c : Fan71c F L) (h83b : Fan83b F L) :
    S.t * S.yMu 2 * S.t = S.yMu 1 * S.zNb 1 := by
  have ht := S.t_sq h71c
  have h6 := S.t_conj_yMu_one F h71c h83b
  have h7 := S.t_conj_zNb_two F h71c
  have hn := S.zNb_one_mul_self F
  have h8 : S.yMu 1 = (S.t * S.yMu 2 * S.t) * S.zNb 1 := by
    calc S.yMu 1 = S.t * (S.t * S.yMu 1 * S.t) * S.t := by
          calc S.yMu 1 = (S.t * S.t) * S.yMu 1 * (S.t * S.t) := by rw [ht]; group
            _ = _ := by group
      _ = S.t * (S.yMu 2 * S.zNb 2) * S.t := by rw [h6]
      _ = (S.t * S.yMu 2 * S.t) * (S.t * S.zNb 2 * S.t) := by
          calc _ = S.t * S.yMu 2 * (S.t * S.t) * S.zNb 2 * S.t := by rw [ht]; group
            _ = _ := by group
      _ = _ := by rw [h7]
  calc S.t * S.yMu 2 * S.t = (S.t * S.yMu 2 * S.t) * (S.zNb 1 * S.zNb 1) := by rw [hn, mul_one]
    _ = ((S.t * S.yMu 2 * S.t) * S.zNb 1) * S.zNb 1 := by group
    _ = S.yMu 1 * S.zNb 1 := by rw [← h8]

end Sec9Cfg

end CFSG.Quasithin.Fan86

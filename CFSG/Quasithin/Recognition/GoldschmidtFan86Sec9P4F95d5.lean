module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95d4

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem zMuij_two_one_three (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L)
    (h82a : Fan82a F L) (h83b : Fan83b F L) (h512 : Fan512 F L) :
    S.zMuij 2 1 * S.zMuij 2 3 = S.ub * S.zNb 2 := by
  have hf := S.fcomm_ub F h71c h81 h82a h83b h512
  have h1 : S.zMuij 2 1 * S.zMuij 2 3 = S.xβ * (S.zMu1 1 * S.zMu1 3) * S.xβ⁻¹ := by
    rw [← S.psi2_zMu1 F, ← S.psi2_zMu1 F]
    group
  have hub : S.xβ * S.ub * S.xβ⁻¹ = S.ub := by
    rw [mul_comm_of_fcomm_eq_one hf, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : S.zMu1 1 * S.zMu1 3 = S.ub * L.z S.α := by
    have hz := L.z_mul_self S.D.val
    rw [S.ub_eq, mul_assoc, hz, mul_one]
  rw [h1, h2]
  calc S.xβ * (S.ub * L.z S.α) * S.xβ⁻¹
      = (S.xβ * S.ub * S.xβ⁻¹) * (S.xβ * L.z S.α * S.xβ⁻¹) := by group
    _ = S.ub * S.zNb 2 := by rw [hub, S.psi2_za F]

theorem yMu_two_eps0 (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) (h82a : Fan82a F L)
    (h83a : Fan83a F L) (h83b : Fan83b F L) (h83d : Fan83d F L) (h87 : Fan87 F L)
    (h512 : Fan512 F L) (hR : P1Rel S.D.x S.w (L.z S.α) S.yEta S.zMu1)
    (hε : S.w * S.w = S.zEta13) : S.yMu 2 = S.yEta 2 * S.ub * S.zNb 2 := by
  have h71c := h7.2.2.1
  obtain ⟨m, hm0, hm2, hm⟩ := S.qv_loc F h7 h83a h83b
  obtain ⟨hwn, -, hp0⟩ := S.w_shape_dt F h7 h83a h83b h87 h512
  obtain ⟨p3, p1, p4⟩ := hp0 hε
  have hq := S.w_fix_qv F h71c
  have hcom := (S.yMu_prod_fcomm F h71c h83b h83d h512 hR).2
  have hy2 : S.yMu 2 * S.yEta 2 = L.z ((S.dt F).alpha 1) * L.z S.qv :=
    S.yMu_two_mul_yEta_two F h71c
  have hmoved : ∀ {m : Fin 5}, S.w • (S.dt F).alpha m ≠ (S.dt F).alpha m →
      ¬ (S.qv = (S.dt F).alpha m ∨ S.qv = (S.dt F).alphaS F m) := by
    intro m hmv hq'
    rcases hq' with h' | h'
    · rw [h'] at hq
      exact hmv hq
    · rw [h'] at hq
      exact (S.dt F).moved_alphaS F hwn hmv hq
  have hm3 : m = 3 := by
    fin_cases m
    · exact absurd rfl hm0
    · exact absurd hm (hmoved p1)
    · exact absurd rfl hm2
    · rfl
    · exact absurd hm (hmoved p4)
  subst hm3
  have hz3 := (S.dt F).za_mul_self F 3
  have hu := S.zMuij_two_one_three F h71c h81 h82a h83b h512
  have hyy2 : S.yEta 2 * S.yEta 2 = 1 := by
    rw [← pow_two]
    exact hR.y2 2
  have hcommu : S.yEta 2 * S.ub = S.ub * S.yEta 2 := by
    rw [S.ub_eq]
    coll hR
  have hcommz : S.yEta 2 * S.zNb 2 = S.zNb 2 * S.yEta 2 := by
    rw [S.zNb_two]
    have := hR.yz 2 2
    simp only [ite_true] at this
    exact mul_comm_of_fcomm_eq_one this
  have hinv : ∀ x : G, x = (x * S.yEta 2) * S.yEta 2 := fun x => by
    calc x = x * (S.yEta 2 * S.yEta 2) := by rw [hyy2, mul_one]
      _ = (x * S.yEta 2) * S.yEta 2 := by group
  rcases hm with h' | h'
  ·
    rw [h'] at hy2
    have hy3 : S.yMu 2 * S.yEta 2 = S.ub * S.zNb 2 := by
      rw [hy2]
      exact hu
    calc S.yMu 2 = (S.yMu 2 * S.yEta 2) * S.yEta 2 := hinv _
      _ = (S.ub * S.zNb 2) * S.yEta 2 := by rw [hy3]
      _ = S.yEta 2 * (S.ub * S.zNb 2) := by
        rw [mul_assoc, ← hcommz, ← mul_assoc, ← hcommu, mul_assoc]
      _ = S.yEta 2 * S.ub * S.zNb 2 := by group
  ·
    exfalso
    rw [h', (S.dt F).z_alphaS F h512 3, S.z_dt_center] at hy2
    have hy3 : S.yMu 2 * S.yEta 2 = S.ub := by
      rw [hy2]
      calc L.z ((S.dt F).alpha 1) * (L.z ((S.dt F).alpha 3) * S.zNb 2)
          = (L.z ((S.dt F).alpha 1) * L.z ((S.dt F).alpha 3)) * S.zNb 2 := by group
        _ = S.ub * S.zNb 2 * S.zNb 2 := by rw [S.z_dt_alpha_one, S.z_dt_alpha_one, hu]
        _ = S.ub := by rw [mul_assoc, S.zNb_two_mul_self F, mul_one]
    have hY : S.yMu 2 = S.yEta 2 * S.ub := by
      calc S.yMu 2 = (S.yMu 2 * S.yEta 2) * S.yEta 2 := hinv _
        _ = S.ub * S.yEta 2 := by rw [hy3]
        _ = S.yEta 2 * S.ub := hcommu.symm
    rw [hY, S.ub_eq] at hcom
    have hcom' : fcomm (S.yEta 2 * (S.zMu1 1 * S.zMu1 3 * L.z S.α)) (S.yEta 0) =
        S.zMu1 3 * S.zMu1 4 := by
      coll hR
    have h2 : fcomm (S.yEta 2 * (S.zMu1 1 * S.zMu1 3 * L.z S.α)) S.t = S.zMu1 3 * S.zMu1 4 :=
      hcom'
    exact L.z_ne_one S.D.val (mul_eq_left.1 (h2.symm.trans hcom).symm)

end Sec9Cfg

end CFSG.Quasithin.Fan86

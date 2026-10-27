module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95d3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95c2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem zNb_two_mul_self (F : FanTree Γ G) : S.zNb 2 * S.zNb 2 = 1 := by
  rw [S.zNb_two]
  exact S.D.za_mul_self F 2

theorem yMu_two_eq (F : FanTree Γ G) :
    S.yMu 2 = L.z ((S.dt F).alpha 0) * L.z ((S.dt F).alpha 1) := rfl

theorem yMu_two_mul_yEta_two (F : FanTree Γ G) (h71c : Fan71c F L) :
    S.yMu 2 * S.yEta 2 = L.z ((S.dt F).alpha 1) * L.z S.qv := by
  rw [S.yMu_two_eq F, S.yEta_two_eq F h71c, ← S.dt_alpha_zero F]
  have hc := (S.dt F).za_comm F h71c 1 0
  have h0 := (S.dt F).za_mul_self F 0
  calc L.z ((S.dt F).alpha 0) * L.z ((S.dt F).alpha 1) *
        (L.z ((S.dt F).alpha 0) * L.z S.qv)
      = L.z ((S.dt F).alpha 0) * (L.z ((S.dt F).alpha 1) * L.z ((S.dt F).alpha 0)) *
        L.z S.qv := by group
    _ = L.z ((S.dt F).alpha 0) * (L.z ((S.dt F).alpha 0) * L.z ((S.dt F).alpha 1)) *
        L.z S.qv := by rw [hc]
    _ = L.z ((S.dt F).alpha 1) * L.z S.qv := by
      calc _ = (L.z ((S.dt F).alpha 0) * L.z ((S.dt F).alpha 0)) * L.z ((S.dt F).alpha 1) *
            L.z S.qv := by group
        _ = _ := by rw [h0, one_mul]

theorem yMu_two_eps1 (F : FanTree Γ G) (h7 : Fan7 F L) (h83a : Fan83a F L) (h83b : Fan83b F L)
    (h83d : Fan83d F L) (h87 : Fan87 F L) (h512 : Fan512 F L)
    (hR : P1Rel S.D.x S.w (L.z S.α) S.yEta S.zMu1)
    (hε : S.w * S.w = S.zEta13 * L.z S.α) : S.yMu 2 = S.yEta 2 * S.zNb 2 := by
  have h71c := h7.2.2.1
  obtain ⟨m, hm0, hm2, hm⟩ := S.qv_loc F h7 h83a h83b
  obtain ⟨hwn, hp1, -⟩ := S.w_shape_dt F h7 h83a h83b h87 h512
  obtain ⟨p1, p3, p4⟩ := hp1 hε
  have hq := S.w_fix_qv F h71c
  have hcom := (S.yMu_prod_fcomm F h71c h83b h83d h512 hR).2
  have hn2 := S.zNb_two_mul_self F
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
  have hm1 : m = 1 := by
    fin_cases m
    · exact absurd rfl hm0
    · rfl
    · exact absurd rfl hm2
    · exact absurd hm (hmoved p3)
    · exact absurd hm (hmoved p4)
  subst hm1
  have hz1 := (S.dt F).za_mul_self F 1
  have hyy2 : S.yEta 2 * S.yEta 2 = 1 := by
    rw [← pow_two]
    exact hR.y2 2
  rcases hm with h' | h'
  ·
    exfalso
    rw [h', hz1] at hy2
    have hY : S.yMu 2 = S.yEta 2 := by
      have h1 : S.yMu 2 = (S.yEta 2)⁻¹ := eq_inv_of_mul_eq_one_left hy2
      rw [h1, P1Rel.y_inv hR]
    rw [hY] at hcom
    have hy := hR.yy 2 0 (by decide)
    have k20 : kstar 2 0 = (3 : Fin 5) := by decide
    have k02 : kstar 0 2 = (4 : Fin 5) := by decide
    rw [k20, k02] at hy
    have h2 : fcomm (S.yEta 2) S.t = S.zMu1 3 * S.zMu1 4 := hy
    exact L.z_ne_one S.D.val (mul_eq_left.1 (h2.symm.trans hcom).symm)
  ·
    rw [h', (S.dt F).z_alphaS F h512 1, S.z_dt_center] at hy2
    have hy3 : S.yMu 2 * S.yEta 2 = S.zNb 2 := by
      rw [hy2]
      calc L.z ((S.dt F).alpha 1) * (L.z ((S.dt F).alpha 1) * S.zNb 2)
          = (L.z ((S.dt F).alpha 1) * L.z ((S.dt F).alpha 1)) * S.zNb 2 := by group
        _ = S.zNb 2 := by rw [hz1, one_mul]
    have hc2 : S.yEta 2 * S.zMu1 2 = S.zMu1 2 * S.yEta 2 := by
      have := hR.yz 2 2
      simp only [ite_true] at this
      exact mul_comm_of_fcomm_eq_one this
    calc S.yMu 2 = S.yMu 2 * (S.yEta 2 * S.yEta 2) := by rw [hyy2, mul_one]
      _ = (S.yMu 2 * S.yEta 2) * S.yEta 2 := by group
      _ = S.zMu1 2 * S.yEta 2 := by rw [hy3, S.zNb_two]; rfl
      _ = S.yEta 2 * S.zNb 2 := by rw [← hc2, S.zNb_two]; rfl

end Sec9Cfg

end CFSG.Quasithin.Fan86

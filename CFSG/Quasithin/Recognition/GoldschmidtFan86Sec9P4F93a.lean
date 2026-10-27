module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Lbl2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L) {F : FanTree Γ G}

theorem reflect_zero (h71c : Fan71c F L) : S.zMu 2 * S.zMu1 0 * S.zMu 2 = S.zMu1 4 := by
  rw [S.zMu_two]
  exact S.D.z_delta_z_alpha F h71c 2 0

theorem comm_zMu01_via_t (h71c : Fan71c F L) (h81 : Fan81 F L) (h83b : Fan83b F L) :
    S.zMu1 0 * S.zMu 1 * S.zMu1 0 * S.zMu 1 = S.zMu1 0 * (L.z S.α * S.zMu1 4) := by
  set φ : G ≃* G := MulAut.conj S.t with hφ
  have hφ' : ∀ x, φ x = S.t * x * S.t := fun x => by
    rw [hφ, MulAut.conj_apply, S.t_inv h71c]
  have h0 : φ (S.zMu1 0) = S.zMu1 0 := by rw [hφ']; exact S.t_conj_zMu1_zero h71c h83b
  have h4 : φ (S.zMu1 4) = L.z S.α * S.zMu1 4 := by
    rw [hφ']; exact S.t_conj_zMu1_ne h71c h83b (by decide)
  have hp : S.zMu 1 = φ (S.zMu 2) := by rw [hφ']; exact S.zMu_one_eq h71c h81
  have hs : S.zMu1 0 * S.zMu 2 * S.zMu1 0 * S.zMu 2 = S.zMu1 0 * S.zMu1 4 := by
    calc S.zMu1 0 * S.zMu 2 * S.zMu1 0 * S.zMu 2
        = S.zMu1 0 * (S.zMu 2 * S.zMu1 0 * S.zMu 2) := by group
      _ = S.zMu1 0 * S.zMu1 4 := by rw [S.reflect_zero h71c]
  calc S.zMu1 0 * S.zMu 1 * S.zMu1 0 * S.zMu 1
      = φ (S.zMu1 0) * φ (S.zMu 2) * φ (S.zMu1 0) * φ (S.zMu 2) := by rw [h0, hp]
    _ = φ (S.zMu1 0 * S.zMu 2 * S.zMu1 0 * S.zMu 2) := by simp only [map_mul]
    _ = φ (S.zMu1 0 * S.zMu1 4) := by rw [hs]
    _ = S.zMu1 0 * (L.z S.α * S.zMu1 4) := by rw [map_mul, h0, h4]

theorem comm_zMu01_via_reflect (h71c : Fan71c F L) :
    S.zMu1 0 * S.zMu 1 * S.zMu1 0 * S.zMu 1 = S.zMuij 1 4 * S.zMu 1 := by
  have h := (S.D.translate F S.xβ⁻¹).z_delta_z_alpha F h71c 2 0
  have e : (2 * 2 - 0 : Fin 5) = 4 := by decide
  rw [e] at h
  have h1 : L.z ((S.D.translate F S.xβ⁻¹).delta 2) = S.zMu1 0 := by
    rw [D10Set.translate_delta, S.xβ_inv_smul_delta2]; rfl
  have h2 : L.z ((S.D.translate F S.xβ⁻¹).alpha 0) = S.zMu 1 := by
    rw [D10Set.translate_alpha, S.zMu_one]
  have h3 : L.z ((S.D.translate F S.xβ⁻¹).alpha 4) = S.zMuij 1 4 := by
    rw [D10Set.translate_alpha, S.zMuij_one]
  rw [h1, h2, h3] at h
  calc S.zMu1 0 * S.zMu 1 * S.zMu1 0 * S.zMu 1
      = (S.zMu1 0 * S.zMu 1 * S.zMu1 0) * S.zMu 1 := by group
    _ = S.zMuij 1 4 * S.zMu 1 := by rw [h]

theorem comm_zMu01 (h71c : Fan71c F L) (h81 : Fan81 F L) (h83b : Fan83b F L) :
    S.zMu1 0 * (L.z S.α * S.zMu1 4) = S.zMuij 1 4 * S.zMu 1 :=
  (S.comm_zMu01_via_t h71c h81 h83b).symm.trans (S.comm_zMu01_via_reflect h71c)

theorem psi_v (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) (h83b : Fan83b F L) :
    MulAut.conj S.xβ⁻¹ (S.zMu1 0 * (L.z S.α * S.zMu1 4)) =
      (S.zMu1 0 * (L.z S.α * S.zMu1 4)) * S.zNb 1 := by
  have hstar := S.comm_zMu01 h71c h81 h83b
  rw [map_mul, map_mul, S.psi_zMu1 F 0, S.psi_zMu1 F 4, S.psi_zalpha, hstar, S.zMu_one_eq_zMuij]
  have h04 : Commute (S.zMuij 1 0) (S.zMuij 1 4) := S.zMuij_one_comm F h71c 0 4
  have hn4 : Commute (S.zMuij 1 4) (S.zNb 1) := S.zMuij_one_comm_nb F h71c 4
  calc S.zMuij 1 0 * (S.zNb 1 * S.zMuij 1 4) = S.zMuij 1 0 * (S.zMuij 1 4 * S.zNb 1) := by
        rw [hn4.eq]
    _ = S.zMuij 1 0 * S.zMuij 1 4 * S.zNb 1 := by rw [mul_assoc]
    _ = S.zMuij 1 4 * S.zMuij 1 0 * S.zNb 1 := by rw [h04.eq]

theorem prod_alpha (F : FanTree Γ G) (h82a : Fan82a F L) :
    S.zMu1 1 * S.zMu1 2 * S.zMu1 3 = S.zMu1 0 * S.zMu1 4 := by
  have h : S.zMu1 0 * S.zMu1 1 * S.zMu1 2 * S.zMu1 3 * S.zMu1 4 = 1 := h82a S.α S.D
  calc S.zMu1 1 * S.zMu1 2 * S.zMu1 3
      = (S.zMu1 0)⁻¹ * (S.zMu1 0 * S.zMu1 1 * S.zMu1 2 * S.zMu1 3 * S.zMu1 4) *
        (S.zMu1 4)⁻¹ := by group
    _ = S.zMu1 0 * S.zMu1 4 := by rw [h, S.zMu1_inv F, S.zMu1_inv F]; group

theorem ub_eq_v (F : FanTree Γ G) (h71c : Fan71c F L) (h82a : Fan82a F L) :
    S.zMu1 1 * S.zMu1 3 * L.z S.α = (S.zMu1 0 * (L.z S.α * S.zMu1 4)) * S.zNb 2 := by
  have hp := S.prod_alpha F h82a
  have hζ4 : Commute (L.z S.α) (S.zMu1 4) := (S.zMu1_comm_alpha F h71c 4).symm
  have hζ2 : Commute (L.z S.α) (S.zMu1 2) := (S.zMu1_comm_alpha F h71c 2).symm
  have h23 : Commute (S.zMu1 2) (S.zMu1 3) := S.zMu1_commute F h71c 2 3
  rw [S.zNb_two]
  show _ = (S.zMu1 0 * (L.z S.α * S.zMu1 4)) * S.zMu1 2
  calc S.zMu1 1 * S.zMu1 3 * L.z S.α
      = S.zMu1 1 * (S.zMu1 3 * S.zMu1 2 * S.zMu1 2) * L.z S.α := by
        rw [mul_assoc (S.zMu1 3), S.zMu1_mul_self F, mul_one]
    _ = S.zMu1 1 * (S.zMu1 2 * S.zMu1 3 * S.zMu1 2) * L.z S.α := by rw [h23.eq]
    _ = (S.zMu1 1 * S.zMu1 2 * S.zMu1 3) * (S.zMu1 2 * L.z S.α) := by group
    _ = (S.zMu1 1 * S.zMu1 2 * S.zMu1 3) * (L.z S.α * S.zMu1 2) := by rw [hζ2.eq]
    _ = (S.zMu1 0 * S.zMu1 4) * (L.z S.α * S.zMu1 2) := by rw [hp]
    _ = S.zMu1 0 * (S.zMu1 4 * L.z S.α) * S.zMu1 2 := by group
    _ = S.zMu1 0 * (L.z S.α * S.zMu1 4) * S.zMu1 2 := by rw [← hζ4.eq]

theorem fcomm_eq_one_of_conj {a b : G} (h : a⁻¹ * b * a = b) : fcomm a b = 1 := by
  have h' : a⁻¹ * b⁻¹ * a = b⁻¹ := by
    have := congrArg (fun y => y⁻¹) h
    simpa [mul_assoc] using this
  show a⁻¹ * b⁻¹ * a * b = 1
  rw [h', inv_mul_cancel]

theorem fcomm_ub (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) (h82a : Fan82a F L)
    (h83b : Fan83b F L) (h512 : Fan512 F L) : fcomm S.xβ S.ub = 1 := by
  apply fcomm_eq_one_of_conj
  have h : MulAut.conj S.xβ⁻¹ S.ub = S.ub := by
    rw [S.ub_eq, S.ub_eq_v F h71c h82a, map_mul, S.psi_v F h71c h81 h83b, S.psi_zNb2 F, mul_assoc,
      S.zNb_one_mul_alpha F h512]
  exact (S.psi_apply S.ub).symm.trans h

end Sec9Cfg

end CFSG.Quasithin.Fan86

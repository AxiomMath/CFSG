module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F93a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L) {F : FanTree Γ G}

theorem sq_01 (h71c : Fan71c F L) (h81 : Fan81 F L) (h83b : Fan83b F L) :
    S.zMu 0 * S.zMu 1 * S.zMu 0 * S.zMu 1 = S.zMu1 0 * (L.z S.α * S.zMu1 4) := by
  rw [S.zMu_zero]
  exact S.comm_zMu01_via_t h71c h81 h83b

theorem sq_12 (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) (h83b : Fan83b F L) :
    S.zMu 1 * S.zMu 2 * S.zMu 1 * S.zMu 2 =
      (S.zMu1 0 * (L.z S.α * S.zMu1 4)) * S.zNb 1 := by
  have hL : MulAut.conj S.xβ⁻¹ (S.zMu 0 * S.zMu 1 * S.zMu 0 * S.zMu 1) =
      S.zMu 1 * S.zMu 2 * S.zMu 1 * S.zMu 2 := by
    simp only [map_mul, S.psi_zMu_zero F, S.psi_zMu_one F]
  calc S.zMu 1 * S.zMu 2 * S.zMu 1 * S.zMu 2
      = MulAut.conj S.xβ⁻¹ (S.zMu 0 * S.zMu 1 * S.zMu 0 * S.zMu 1) := hL.symm
    _ = MulAut.conj S.xβ⁻¹ (S.zMu1 0 * (L.z S.α * S.zMu1 4)) := by rw [S.sq_01 h71c h81 h83b]
    _ = (S.zMu1 0 * (L.z S.α * S.zMu1 4)) * S.zNb 1 := S.psi_v F h71c h81 h83b

theorem sq_20 (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) (h83b : Fan83b F L)
    (h512 : Fan512 F L) :
    S.zMu 2 * S.zMu 0 * S.zMu 2 * S.zMu 0 = (S.zMu1 0 * (L.z S.α * S.zMu1 4)) * L.z S.α := by
  have hL : MulAut.conj S.xβ⁻¹ (S.zMu 1 * S.zMu 2 * S.zMu 1 * S.zMu 2) =
      S.zMu 2 * S.zMu 0 * S.zMu 2 * S.zMu 0 := by
    simp only [map_mul, S.psi_zMu_one F, S.psi_zMu_two F]
  calc S.zMu 2 * S.zMu 0 * S.zMu 2 * S.zMu 0
      = MulAut.conj S.xβ⁻¹ (S.zMu 1 * S.zMu 2 * S.zMu 1 * S.zMu 2) := hL.symm
    _ = MulAut.conj S.xβ⁻¹ ((S.zMu1 0 * (L.z S.α * S.zMu1 4)) * S.zNb 1) := by
        rw [S.sq_12 F h71c h81 h83b]
    _ = (S.zMu1 0 * (L.z S.α * S.zMu1 4)) * S.zNb 1 * S.zNb 2 := by
        rw [map_mul, S.psi_v F h71c h81 h83b, S.psi_zNb1 F]
    _ = (S.zMu1 0 * (L.z S.α * S.zMu1 4)) * L.z S.α := by
        rw [mul_assoc _ (S.zNb 1), S.zNb_one_mul_zNb_two F h512]

theorem zeta_comm_zMu0 (F : FanTree Γ G) (h71c : Fan71c F L) : Commute (L.z S.α) (S.zMu 0) := by
  rw [S.zMu_zero]; exact (S.zMu1_comm_alpha F h71c 0).symm

theorem zeta_comm_zMu1 (F : FanTree Γ G) (h71c : Fan71c F L) : Commute (L.z S.α) (S.zMu 1) := by
  have h := (S.zMu1_commute F h71c 2 0).map (MulAut.conj S.xβ⁻¹)
  have e1 : MulAut.conj S.xβ⁻¹ (S.zMu1 2) = L.z S.α := by
    have := S.psi_zNb2 F
    rwa [S.zNb_two] at this
  have e2 : MulAut.conj S.xβ⁻¹ (S.zMu1 0) = S.zMu 1 := by
    rw [S.psi_zMu1 F 0, ← S.zMu_one_eq_zMuij]
  rw [e1, e2] at h
  exact h

theorem zeta_comm_zMu2 (F : FanTree Γ G) (h71c : Fan71c F L) : Commute (L.z S.α) (S.zMu 2) := by
  rw [S.zMu_two]; exact (S.D.zd_comm_start F h71c 2).symm

theorem v_comm_zMu0 (F : FanTree Γ G) (h71c : Fan71c F L) :
    Commute (S.zMu1 0 * (L.z S.α * S.zMu1 4)) (S.zMu 0) := by
  rw [S.zMu_zero]
  exact ((Commute.refl _).mul_right ((S.zMu1_comm_alpha F h71c 0).mul_right
    (S.zMu1_commute F h71c 0 4))).symm

theorem v_comm_alpha (F : FanTree Γ G) (h71c : Fan71c F L) :
    Commute (S.zMu1 0 * (L.z S.α * S.zMu1 4)) (L.z S.α) :=
  (S.zMu1_comm_alpha F h71c 0).mul_left ((Commute.refl _).mul_left (S.zMu1_comm_alpha F h71c 4))

theorem v_comm_zMu1 (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L)
    (h83b : Fan83b F L) : Commute (S.zMu1 0 * (L.z S.α * S.zMu1 4)) (S.zMu 1) := by
  rw [S.comm_zMu01 h71c h81 h83b, S.zMu_one_eq_zMuij]
  exact (S.zMuij_one_comm F h71c 4 0).mul_left (Commute.refl _)

theorem v_mul_self (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L)
    (h83b : Fan83b F L) :
    (S.zMu1 0 * (L.z S.α * S.zMu1 4)) * (S.zMu1 0 * (L.z S.α * S.zMu1 4)) = 1 := by
  rw [S.comm_zMu01 h71c h81 h83b]
  have hc := S.zMuij_one_comm F h71c 4 0
  calc S.zMuij 1 4 * S.zMu 1 * (S.zMuij 1 4 * S.zMu 1)
      = S.zMuij 1 4 * (S.zMu 1 * S.zMuij 1 4) * S.zMu 1 := by group
    _ = S.zMuij 1 4 * (S.zMuij 1 4 * S.zMu 1) * S.zMu 1 := by
        rw [S.zMu_one_eq_zMuij, ← hc.eq]
    _ = (S.zMuij 1 4 * S.zMuij 1 4) * (S.zMu 1 * S.zMu 1) := by group
    _ = 1 := by rw [S.zMuij_one_mul_self F, S.zMu_one_mul_self F, mul_one]

theorem zMu_rot (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) (h83b : Fan83b F L)
    (h512 : Fan512 F L) :
    S.zMu 1 * S.zMu 2 * S.zMu 0 = S.zMu 0 * S.zMu 1 * S.zMu 2 * L.z S.α := by
  have h1 := S.sq_01 h71c h81 h83b
  have h3 := S.sq_20 F h71c h81 h83b h512
  have h00 := S.zMu_zero_mul_self F
  have h11 := S.zMu_one_mul_self F
  have h22 := S.zMu_two_mul_self F
  have hv0 := S.v_comm_zMu0 F h71c
  have hv1 := S.v_comm_zMu1 F h71c h81 h83b
  have hvζ := S.v_comm_alpha F h71c
  have hv2 := S.v_mul_self F h71c h81 h83b
  have hζ0 := S.zeta_comm_zMu0 F h71c
  have hζ1 := S.zeta_comm_zMu1 F h71c
  have hζ2 := S.zeta_comm_zMu2 F h71c
  set v := S.zMu1 0 * (L.z S.α * S.zMu1 4) with hv
  set ζ := L.z S.α with hζ
  set p0 := S.zMu 0
  set p1 := S.zMu 1
  set p2 := S.zMu 2
  have h20 : p2 * p0 = (v * ζ) * (p0 * p2) := by
    have e : p2 * p0 * p2 * p0 * (p0 * p2) = p2 * p0 := by
      calc p2 * p0 * p2 * p0 * (p0 * p2) = p2 * p0 * p2 * (p0 * p0) * p2 := by group
        _ = p2 * p0 * p2 * p2 := by rw [h00, mul_one]
        _ = p2 * p0 * (p2 * p2) := by group
        _ = p2 * p0 := by rw [h22, mul_one]
    rw [← e, h3]
  have h10 : p1 * p0 = p0 * v * p1 := by
    have e : p0 * (p0 * p1 * p0 * p1) * p1 = p1 * p0 := by
      calc p0 * (p0 * p1 * p0 * p1) * p1 = (p0 * p0) * p1 * p0 * (p1 * p1) := by group
        _ = p1 * p0 := by rw [h00, h11, one_mul, mul_one]
    rw [← e, h1]
  have hc1 : Commute p1 (v * ζ) := (hv1.symm.mul_right hζ1.symm)
  calc p1 * p2 * p0 = p1 * (p2 * p0) := by group
    _ = p1 * ((v * ζ) * (p0 * p2)) := by rw [h20]
    _ = (v * ζ) * (p1 * (p0 * p2)) := hc1.left_comm _
    _ = (v * ζ) * ((p1 * p0) * p2) := by group
    _ = (v * ζ) * ((p0 * v * p1) * p2) := by rw [h10]
    _ = v * ζ * (p0 * v) * p1 * p2 := by group
    _ = v * ζ * (v * p0) * p1 * p2 := by rw [hv0.symm.eq]
    _ = v * (ζ * v) * p0 * p1 * p2 := by group
    _ = v * (v * ζ) * p0 * p1 * p2 := by rw [hvζ.symm.eq]
    _ = (v * v) * ζ * p0 * p1 * p2 := by group
    _ = ζ * p0 * p1 * p2 := by rw [hv2, one_mul]
    _ = p0 * ζ * p1 * p2 := by rw [hζ0.eq]
    _ = p0 * (ζ * p1) * p2 := by group
    _ = p0 * (p1 * ζ) * p2 := by rw [hζ1.eq]
    _ = p0 * p1 * (ζ * p2) := by group
    _ = p0 * p1 * (p2 * ζ) := by rw [hζ2.eq]
    _ = p0 * p1 * p2 * ζ := by group

theorem fcomm_ubs (F : FanTree Γ G) (h71c : Fan71c F L) (h81 : Fan81 F L) (h83b : Fan83b F L)
    (h512 : Fan512 F L) : fcomm S.xβ S.ubs = 1 := by
  apply fcomm_eq_one_of_conj
  have h : MulAut.conj S.xβ⁻¹ S.ubs = S.ubs := by
    rw [S.ubs_eq, map_mul, map_mul, map_mul, S.psi_zMu_zero F, S.psi_zMu_one F, S.psi_zMu_two F,
      S.psi_zNb1 F, S.zMu_rot F h71c h81 h83b h512, mul_assoc _ (L.z S.α),
      S.zalpha_mul_zNb_two F h71c h512]
  exact (S.psi_apply S.ubs).symm.trans h

end Sec9Cfg

theorem fan_9_3 (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h82 : Fan82 F L) (h83 : Fan83 F L) (h512 : Fan512 F L) : Fan93 F L := by
  intro S
  exact ⟨S.fcomm_ub F h7.2.2.1 h81 h82.1 h83.2.1 h512,
    S.fcomm_ubs F h7.2.2.1 h81 h83.2.1 h512⟩

end CFSG.Quasithin.Fan86

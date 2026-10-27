module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Lbl2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Alg

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L) {F : FanTree Γ G}

theorem xβ_mul_mul : S.xβ * S.xβ * S.xβ = 1 := by
  rw [← pow_two, ← pow_succ]
  exact S.xβ_pow_three

theorem xβ_mul_self : S.xβ * S.xβ = S.xβ⁻¹ := eq_inv_of_mul_eq_one_left S.xβ_mul_mul

theorem xβ_inv_mul_inv : S.xβ⁻¹ * S.xβ⁻¹ = S.xβ := by
  rw [← mul_inv_rev, S.xβ_mul_self, inv_inv]

theorem psi_psi (g : G) :
    MulAut.conj S.xβ⁻¹ (MulAut.conj S.xβ⁻¹ g) = S.xβ * g * S.xβ⁻¹ := by
  rw [S.psi_apply, S.psi_apply]
  calc S.xβ⁻¹ * (S.xβ⁻¹ * g * S.xβ) * S.xβ = (S.xβ⁻¹ * S.xβ⁻¹) * g * (S.xβ * S.xβ) := by group
    _ = S.xβ * g * S.xβ⁻¹ := by rw [S.xβ_inv_mul_inv, S.xβ_mul_self]

theorem zMuij_two (j : Fin 5) : S.zMuij 2 j = L.z ((S.xβ ^ 2)⁻¹ • S.D.alpha j) := rfl

theorem psi_zMuij_one (F : FanTree Γ G) (j : Fin 5) :
    MulAut.conj S.xβ⁻¹ (S.zMuij 1 j) = S.zMuij 2 j := by
  rw [S.zMuij_one, S.zMuij_two, S.xβ_pow_two_inv_smul,
    L.equivariant S.xβ⁻¹ _ ((valence_smul F S.xβ⁻¹ _).trans (S.D.valence_alpha F j))]
  rfl

theorem psi_zMuij_two (F : FanTree Γ G) (j : Fin 5) :
    MulAut.conj S.xβ⁻¹ (S.zMuij 2 j) = S.zMu1 j := by
  have h : S.xβ⁻¹ • (S.xβ ^ 2)⁻¹ • S.D.alpha j = S.D.alpha j := by
    rw [← mul_smul]
    have : S.xβ⁻¹ * (S.xβ ^ 2)⁻¹ = 1 := by
      rw [← mul_inv_rev, ← pow_succ, S.xβ_pow_three, inv_one]
    rw [this, one_smul]
  have h2 := L.equivariant S.xβ⁻¹ ((S.xβ ^ 2)⁻¹ • S.D.alpha j)
    ((valence_smul F _ _).trans (S.D.valence_alpha F j))
  rw [h] at h2
  rw [S.zMuij_two]
  show S.xβ⁻¹ * _ * S.xβ⁻¹⁻¹ = _
  rw [← h2]
  rfl

theorem psi_yMu_zero (F : FanTree Γ G) : MulAut.conj S.xβ⁻¹ (S.yMu 0) = S.yMu 1 := by
  show MulAut.conj S.xβ⁻¹ (S.zMuij 0 0 * S.zMuij 0 1) = S.zMuij 1 0 * S.zMuij 1 1
  rw [map_mul, S.zMuij_zero, S.zMuij_zero, S.psi_zMu1 F, S.psi_zMu1 F]

theorem psi_yMu_one (F : FanTree Γ G) : MulAut.conj S.xβ⁻¹ (S.yMu 1) = S.yMu 2 := by
  show MulAut.conj S.xβ⁻¹ (S.zMuij 1 0 * S.zMuij 1 1) = S.zMuij 2 0 * S.zMuij 2 1
  rw [map_mul, S.psi_zMuij_one F, S.psi_zMuij_one F]

theorem psi_yMu_two (F : FanTree Γ G) : MulAut.conj S.xβ⁻¹ (S.yMu 2) = S.yMu 0 := by
  show MulAut.conj S.xβ⁻¹ (S.zMuij 2 0 * S.zMuij 2 1) = S.zMuij 0 0 * S.zMuij 0 1
  rw [map_mul, S.psi_zMuij_two F, S.psi_zMuij_two F, S.zMuij_zero, S.zMuij_zero]

theorem zMuij_two_comm (F : FanTree Γ G) (h71c : Fan71c F L) (j k : Fin 5) :
    Commute (S.zMuij 2 j) (S.zMuij 2 k) := by
  have h := (S.D.translate F (S.xβ ^ 2)⁻¹).za_comm F h71c j k
  exact h

theorem zMuij_two_comm_nb (F : FanTree Γ G) (h71c : Fan71c F L) (j : Fin 5) :
    Commute (S.zMuij 2 j) (S.zNb 2) := by
  have h := (S.D.translate F (S.xβ ^ 2)⁻¹).za_comm_start F h71c j
  rw [S.zNb_two, ← S.collar_one]
  exact h

theorem zMuij_two_mul_self (F : FanTree Γ G) (j : Fin 5) : S.zMuij 2 j * S.zMuij 2 j = 1 :=
  (S.D.translate F (S.xβ ^ 2)⁻¹).za_mul_self F j

theorem yMu_zero_mul_self (F : FanTree Γ G) (h71c : Fan71c F L) :
    S.yMu 0 * S.yMu 0 = 1 := by
  show S.zMuij 0 0 * S.zMuij 0 1 * (S.zMuij 0 0 * S.zMuij 0 1) = 1
  rw [S.zMuij_zero, S.zMuij_zero]
  exact mul_mul_self_eq_one (S.zMu1_mul_self F 0) (S.zMu1_mul_self F 1)
    (S.zMu1_commute F h71c 0 1).eq

theorem yMu_one_mul_self (F : FanTree Γ G) (h71c : Fan71c F L) :
    S.yMu 1 * S.yMu 1 = 1 :=
  mul_mul_self_eq_one (S.zMuij_one_mul_self F 0) (S.zMuij_one_mul_self F 1)
    (S.zMuij_one_comm F h71c 0 1).eq

theorem yMu_two_mul_self (F : FanTree Γ G) (h71c : Fan71c F L) :
    S.yMu 2 * S.yMu 2 = 1 :=
  mul_mul_self_eq_one (S.zMuij_two_mul_self F 0) (S.zMuij_two_mul_self F 1)
    (S.zMuij_two_comm F h71c 0 1).eq

end Sec9Cfg

end CFSG.Quasithin.Fan86

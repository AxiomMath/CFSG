module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Lbl
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Tr

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L) {F : FanTree Γ G}

theorem zNb_prod (F : FanTree Γ G) (h512 : Fan512 F L) :
    L.z S.α * S.zNb 1 * S.zNb 2 = 1 := by
  rw [S.zNb_one, S.zNb_two]
  have hne1 : S.α ≠ S.xβ⁻¹ • S.α := fun h => S.alpha_ne_xβ_inv h.symm
  have hne2 : S.α ≠ S.D.alpha 2 := fun h => S.D.alpha_ne_start 2 h.symm
  exact h512.2.2.1 S.beta S.α (S.xβ⁻¹ • S.α) (S.D.alpha 2) (S.D.valence_beta F 2)
    (S.neighborSet_beta F) hne1 hne2 S.xβ_inv_alpha_ne_alpha2

theorem zMu1_commute (F : FanTree Γ G) (h71c : Fan71c F L) (j k : Fin 5) :
    Commute (S.zMu1 j) (S.zMu1 k) := S.D.za_comm F h71c j k

theorem zMu1_comm_alpha (F : FanTree Γ G) (h71c : Fan71c F L) (j : Fin 5) :
    Commute (S.zMu1 j) (L.z S.α) := S.D.za_comm_start F h71c j

theorem zMuij_one_comm (F : FanTree Γ G) (h71c : Fan71c F L) (j k : Fin 5) :
    Commute (S.zMuij 1 j) (S.zMuij 1 k) := by
  have h := (S.D.translate F S.xβ⁻¹).za_comm F h71c j k
  rw [D10Set.translate_alpha, D10Set.translate_alpha, ← S.zMuij_one, ← S.zMuij_one] at h
  exact h

theorem zMuij_one_comm_nb (F : FanTree Γ G) (h71c : Fan71c F L) (j : Fin 5) :
    Commute (S.zMuij 1 j) (S.zNb 1) := by
  have h := (S.D.translate F S.xβ⁻¹).za_comm_start F h71c j
  rw [D10Set.translate_alpha, ← S.zMuij_one] at h
  rw [S.zNb_one]
  exact h

theorem zMu1_inv (F : FanTree Γ G) (j : Fin 5) : (S.zMu1 j)⁻¹ = S.zMu1 j :=
  S.D.za_inv F j

theorem zMu1_mul_self (F : FanTree Γ G) (j : Fin 5) : S.zMu1 j * S.zMu1 j = 1 :=
  S.D.za_mul_self F j

theorem zMuij_one_mul_self (F : FanTree Γ G) (j : Fin 5) : S.zMuij 1 j * S.zMuij 1 j = 1 := by
  have h := (S.D.translate F S.xβ⁻¹).za_mul_self F j
  rw [D10Set.translate_alpha, ← S.zMuij_one] at h
  exact h

theorem zMu_zero_mul_self (F : FanTree Γ G) : S.zMu 0 * S.zMu 0 = 1 := by
  rw [S.zMu_zero]; exact S.D.za_mul_self F 0

theorem zMu_one_mul_self (F : FanTree Γ G) : S.zMu 1 * S.zMu 1 = 1 := by
  rw [S.zMu_one]
  exact L.z_mul_self ((valence_smul F S.xβ⁻¹ _).trans (S.D.valence_alpha F 0))

theorem zMu_two_mul_self (F : FanTree Γ G) : S.zMu 2 * S.zMu 2 = 1 := by
  rw [S.zMu_two]; exact S.D.zd_mul_self F 2

theorem zNb_one_mul_zNb_two (F : FanTree Γ G) (h512 : Fan512 F L) :
    S.zNb 1 * S.zNb 2 = L.z S.α := by
  have h := S.zNb_prod F h512
  have := eq_inv_of_mul_eq_one_right (show L.z S.α * (S.zNb 1 * S.zNb 2) = 1 by
    rw [← mul_assoc]; exact h)
  rw [this, L.z_inv S.D.val]

theorem zNb_one_mul_alpha (F : FanTree Γ G) (h512 : Fan512 F L) :
    S.zNb 1 * L.z S.α = S.zNb 2 := by
  have h := S.zNb_prod F h512
  have h1 : S.zNb 1 * S.zNb 2 = L.z S.α := by
    have := eq_inv_of_mul_eq_one_right (show L.z S.α * (S.zNb 1 * S.zNb 2) = 1 by
      rw [← mul_assoc]; exact h)
    rw [this, L.z_inv S.D.val]
  have h2 : S.zNb 1 * S.zNb 1 = 1 := by
    rw [S.zNb_one]
    exact L.z_mul_self ((valence_smul F S.xβ⁻¹ S.α).trans S.D.val)
  calc S.zNb 1 * L.z S.α = S.zNb 1 * (S.zNb 1 * S.zNb 2) := by rw [h1]
    _ = (S.zNb 1 * S.zNb 1) * S.zNb 2 := by rw [mul_assoc]
    _ = S.zNb 2 := by rw [h2, one_mul]

theorem zalpha_mul_zNb_two (F : FanTree Γ G) (h71c : Fan71c F L) (h512 : Fan512 F L) :
    L.z S.α * S.zNb 2 = S.zNb 1 := by
  have hc : Commute (S.zNb 1) (L.z S.α) := by
    have h := (S.zMu1_comm_alpha F h71c 2).symm.map (MulAut.conj S.xβ⁻¹)
    have e1 : MulAut.conj S.xβ⁻¹ (S.zMu1 2) = L.z S.α := by
      have := S.psi_zNb2 F
      rwa [S.zNb_two] at this
    rw [e1, S.psi_zalpha] at h
    exact h
  have h2 : L.z S.α * L.z S.α = 1 := L.z_mul_self S.D.val
  rw [← S.zNb_one_mul_alpha F h512]
  calc L.z S.α * (S.zNb 1 * L.z S.α) = (L.z S.α * S.zNb 1) * L.z S.α := by group
    _ = (S.zNb 1 * L.z S.α) * L.z S.α := by rw [hc.eq]
    _ = S.zNb 1 * (L.z S.α * L.z S.α) := by group
    _ = S.zNb 1 := by rw [h2, mul_one]

end Sec9Cfg

end CFSG.Quasithin.Fan86

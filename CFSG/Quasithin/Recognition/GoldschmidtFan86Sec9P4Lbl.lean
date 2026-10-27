module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Cfg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Lab

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L) {F : FanTree Γ G}

theorem zMu_zero : S.zMu 0 = L.z (S.D.alpha 0) := by
  simp [Sec9Cfg.zMu, D10Set.bv, D10Set.alpha]

theorem zMu_one : S.zMu 1 = L.z (S.xβ⁻¹ • S.D.alpha 0) := by
  simp [Sec9Cfg.zMu, D10Set.bv, D10Set.alpha]

theorem zMu_two : S.zMu 2 = L.z (S.D.delta 2) := by
  show L.z (S.D.bv S.xβ 2 3) = _
  rw [show S.D.bv S.xβ 2 3 = (S.xβ ^ 2)⁻¹ • S.D.alpha 0 from rfl, S.collar_three]

theorem zNb_zero : S.zNb 0 = L.z S.α := by
  simp [Sec9Cfg.zNb, D10Set.bv, S.D.start 0]

theorem zNb_one : S.zNb 1 = L.z (S.xβ⁻¹ • S.α) := by
  simp [Sec9Cfg.zNb, D10Set.bv, S.D.start 0]

theorem zNb_two : S.zNb 2 = L.z (S.D.alpha 2) := by
  show L.z (S.D.bv S.xβ 2 1) = _
  rw [show S.D.bv S.xβ 2 1 = (S.xβ ^ 2)⁻¹ • S.α by simp [D10Set.bv, S.D.start 0],
    S.collar_one]

theorem ub_eq : S.ub = S.zMu1 1 * S.zMu1 3 * L.z S.α := by
  simp [Sec9Cfg.ub, Sec9Cfg.zMuij, Sec9Cfg.zMu1]

theorem ubs_eq : S.ubs = S.zMu 0 * S.zMu 1 * S.zMu 2 * S.zNb 1 := rfl

theorem zMuij_one (j : Fin 5) : S.zMuij 1 j = L.z (S.xβ⁻¹ • S.D.alpha j) := by
  simp [Sec9Cfg.zMuij]

theorem zMuij_zero (j : Fin 5) : S.zMuij 0 j = S.zMu1 j := by
  simp [Sec9Cfg.zMuij, Sec9Cfg.zMu1]

theorem zMu_one_eq_zMuij : S.zMu 1 = S.zMuij 1 0 := by
  rw [S.zMu_one, S.zMuij_one]

theorem zMu_one_eq (h71c : Fan71c F L) (h81 : Fan81 F L) :
    S.zMu 1 = S.t * S.zMu 2 * S.t := by
  rw [S.zMu_one, S.zMu_two, ← S.t_smul_delta2 h71c h81,
    L.equivariant S.t _ (S.D.valence_delta F 2), S.t_inv h71c]

theorem t_conj_zMu1_zero (h71c : Fan71c F L) (h83b : Fan83b F L) :
    S.t * S.zMu1 0 * S.t = S.zMu1 0 := by
  have h := h83b S.α S.D S.η' S.isBeta.pair 0 0
  simp only [ite_true] at h
  have h1 : S.t * L.z (S.D.alpha 0) * S.t * L.z (S.D.alpha 0) = 1 := by
    have : fcomm S.t (L.z (S.D.alpha 0)) = S.t⁻¹ * (L.z (S.D.alpha 0))⁻¹ * S.t *
      L.z (S.D.alpha 0) := rfl
    rw [S.t_inv h71c, S.D.za_inv F] at this
    rw [← this]; exact h
  exact mul_eq_one_iff_eq_inv.1 h1 |>.trans (S.D.za_inv F 0)

theorem t_conj_zMu1_ne (h71c : Fan71c F L) (h83b : Fan83b F L) {j : Fin 5} (hj : j ≠ 0) :
    S.t * S.zMu1 j * S.t = L.z S.α * S.zMu1 j := by
  have h := h83b S.α S.D S.η' S.isBeta.pair 0 j
  have hj' : ¬ ((0 : Fin 5) = j) := fun e => hj e.symm
  simp only [hj', ite_false] at h
  have h1 : S.t * L.z (S.D.alpha j) * S.t * L.z (S.D.alpha j) = L.z S.α := by
    have : fcomm S.t (L.z (S.D.alpha j)) = S.t⁻¹ * (L.z (S.D.alpha j))⁻¹ * S.t *
      L.z (S.D.alpha j) := rfl
    rw [S.t_inv h71c, S.D.za_inv F] at this
    rw [← this]; exact h
  have h2 := congrArg (fun y => y * (L.z (S.D.alpha j))⁻¹) h1
  simp only [mul_assoc, mul_inv_cancel, mul_one] at h2
  rw [S.D.za_inv F] at h2
  show S.t * L.z (S.D.alpha j) * S.t = L.z S.α * L.z (S.D.alpha j)
  rw [mul_assoc]
  exact h2

theorem psi_apply (x : G) : MulAut.conj S.xβ⁻¹ x = S.xβ⁻¹ * x * S.xβ := by
  rw [MulAut.conj_apply, inv_inv]

theorem psi_zMu1 (F : FanTree Γ G) (j : Fin 5) :
    MulAut.conj S.xβ⁻¹ (S.zMu1 j) = S.zMuij 1 j := by
  rw [S.zMuij_one, L.equivariant S.xβ⁻¹ _ (S.D.valence_alpha F j)]
  rfl

theorem psi_zalpha : MulAut.conj S.xβ⁻¹ (L.z S.α) = S.zNb 1 := by
  rw [S.zNb_one, L.equivariant S.xβ⁻¹ _ S.D.val]
  rfl

theorem psi_zNb1 (F : FanTree Γ G) : MulAut.conj S.xβ⁻¹ (S.zNb 1) = S.zNb 2 := by
  rw [S.zNb_one, S.zNb_two, ← S.xβ_inv_smul_xβ_inv_alpha,
    L.equivariant S.xβ⁻¹ _ ((valence_smul F S.xβ⁻¹ S.α).trans S.D.val)]
  rfl

theorem psi_zNb2 (F : FanTree Γ G) : MulAut.conj S.xβ⁻¹ (S.zNb 2) = L.z S.α := by
  have h := L.equivariant S.xβ⁻¹ (S.D.alpha 2) (S.D.valence_alpha F 2)
  rw [S.xβ_inv_smul_alpha2] at h
  rw [S.zNb_two, h]
  rfl

theorem psi_zMu_zero (F : FanTree Γ G) : MulAut.conj S.xβ⁻¹ (S.zMu 0) = S.zMu 1 := by
  rw [S.zMu_zero, S.zMu_one, L.equivariant S.xβ⁻¹ _ (S.D.valence_alpha F 0)]
  rfl

theorem psi_zMu_one (F : FanTree Γ G) : MulAut.conj S.xβ⁻¹ (S.zMu 1) = S.zMu 2 := by
  rw [S.zMu_one, S.zMu_two, ← S.collar_three, S.xβ_pow_two_inv_smul,
    L.equivariant S.xβ⁻¹ _ ((valence_smul F S.xβ⁻¹ _).trans (S.D.valence_alpha F 0))]
  rfl

theorem psi_zMu_two (F : FanTree Γ G) : MulAut.conj S.xβ⁻¹ (S.zMu 2) = S.zMu 0 := by
  have h := L.equivariant S.xβ⁻¹ (S.D.delta 2) (S.D.valence_delta F 2)
  rw [S.xβ_inv_smul_delta2] at h
  rw [S.zMu_two, S.zMu_zero, h]
  rfl

end Sec9Cfg

end CFSG.Quasithin.Fan86

module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95Psi
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Rel

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem xβ_pow_two_inv : (S.xβ ^ 2)⁻¹ = S.xβ := by
  rw [pow_two, S.xβ_mul_self, inv_inv]

@[expose] def dt (F : FanTree Γ G) : D10Set L ((S.xβ ^ 2)⁻¹ • S.α) :=
  S.D.translate F (S.xβ ^ 2)⁻¹

theorem dt_alpha (F : FanTree Γ G) (j : Fin 5) :
    (S.dt F).alpha j = (S.xβ ^ 2)⁻¹ • S.D.alpha j := rfl

theorem dt_alpha_zero (F : FanTree Γ G) : (S.dt F).alpha 0 = S.D.delta 2 := by
  rw [S.dt_alpha]
  exact S.collar_three

theorem dt_beta_two (F : FanTree Γ G) : (S.dt F).beta 2 = S.D.beta 2 := by
  show (S.xβ ^ 2)⁻¹ • S.D.beta 2 = S.D.beta 2
  exact inv_smul_eq_iff.2 (MulAction.mem_stabilizer_iff.1
    (Subgroup.pow_mem _ (MulAction.mem_stabilizer_iff.2 S.xβ_smul_beta) 2)).symm

theorem dt_alpha_two (F : FanTree Γ G) : (S.dt F).alpha 2 = S.xβ⁻¹ • S.α := by
  rw [S.dt_alpha, ← S.collar_one, ← mul_smul, S.xβ_pow_two_inv, S.xβ_mul_self]

theorem z_dt_alpha_zero (F : FanTree Γ G) : L.z ((S.dt F).alpha 0) = S.zEta13 := by
  rw [S.dt_alpha_zero]
  rfl

theorem z_dt_alpha_two (F : FanTree Γ G) : L.z ((S.dt F).alpha 2) = S.zNb 1 := by
  rw [S.dt_alpha_two, S.zNb_one]

theorem z_dt_center : L.z ((S.xβ ^ 2)⁻¹ • S.α) = S.zNb 2 := by
  rw [S.collar_one, S.zNb_two]

theorem z_dt_alpha_one (F : FanTree Γ G) (j : Fin 5) :
    L.z ((S.dt F).alpha j) = S.zMuij 2 j := rfl

theorem w_fix_xβ_inv_alpha (F : FanTree Γ G) : S.w • (S.xβ⁻¹ • S.α) = S.xβ⁻¹ • S.α := by
  have hwα : S.w • S.α = S.α := MulAction.mem_stabilizer_iff.1 S.w_mem_stabilizer
  have hwβ : S.w • S.beta = S.beta := S.w_fix_vert 1 (by norm_num)
  have hw3 : S.w • S.D.alpha 2 = S.D.alpha 2 := S.w_fix_alpha2
  have hadj : S.xβ⁻¹ • S.α ∈ Γ.neighborSet S.beta := by
    rw [S.neighborSet_beta F]
    simp
  have h1 : Γ.Adj S.beta (S.w • (S.xβ⁻¹ • S.α)) := by
    have := (F.adj_smul S.w S.beta _).2 hadj
    rwa [hwβ] at this
  have h2 : S.w • (S.xβ⁻¹ • S.α) ∈ Γ.neighborSet S.beta := h1
  rw [S.neighborSet_beta F] at h2
  rcases h2 with h | h | h
  · exact absurd (MulAction.injective S.w (h.trans hwα.symm)) S.alpha_ne_xβ_inv
  · exact h
  · exact absurd (MulAction.injective S.w (h.trans hw3.symm)) S.xβ_inv_alpha_ne_alpha2

theorem dt_w_fixes (F : FanTree Γ G) :
    S.w • (S.dt F).alpha 0 = (S.dt F).alpha 0 ∧ S.w • (S.dt F).alpha 2 = (S.dt F).alpha 2 := by
  rw [S.dt_alpha_zero, S.dt_alpha_two]
  exact ⟨S.w_fix_vert 4 (by norm_num), S.w_fix_xβ_inv_alpha F⟩

end Sec9Cfg

end CFSG.Quasithin.Fan86

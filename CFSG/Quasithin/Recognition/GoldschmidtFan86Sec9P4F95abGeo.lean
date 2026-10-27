module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Gen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Lbl2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Card

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem f95_wA_eq : S.wA 1 = S.xβ⁻¹ * S.w * S.xβ := by simp [wA]

theorem f95_cA_eq : S.cA 1 = S.xβ⁻¹ * S.c * S.xβ := by simp [cA]

theorem f95_xβ_smul_alpha0 : S.xβ • S.D.alpha 0 = S.D.delta 2 := by
  rw [eq_comm, ← inv_smul_eq_iff]
  exact S.xβ_inv_smul_delta2

theorem f95_xβ_smul_alpha2 : S.xβ • S.D.alpha 2 = S.xβ⁻¹ • S.α := by
  rw [← S.xβ_inv_smul_xβ_inv_alpha, smul_inv_smul]

theorem f95_fix_third (F : FanTree Γ G) {g : G} (hα : g • S.α = S.α) (hβ : g • S.beta = S.beta)
    (hα2 : g • S.D.alpha 2 = S.D.alpha 2) : g • (S.xβ⁻¹ • S.α) = S.xβ⁻¹ • S.α := by
  have hmem : S.xβ⁻¹ • S.α ∈ Γ.neighborSet S.beta := by
    rw [S.neighborSet_beta F]
    simp
  have hadj : Γ.Adj S.beta (g • (S.xβ⁻¹ • S.α)) := by
    have := (F.adj_smul g S.beta (S.xβ⁻¹ • S.α)).2 hmem
    rwa [hβ] at this
  have hmem' : g • (S.xβ⁻¹ • S.α) ∈ Γ.neighborSet S.beta := hadj
  rw [S.neighborSet_beta F] at hmem'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem'
  rcases hmem' with h | h | h
  · exact absurd (MulAction.injective g (h.trans hα.symm)) S.alpha_ne_xβ_inv
  · exact h
  · exact absurd (MulAction.injective g (h.trans hα2.symm)) S.xβ_inv_alpha_ne_alpha2

theorem f95_psi_fixes (F : FanTree Γ G) {g : G} (hg : g ∈ (S.D.P 2).stab G) :
    (S.xβ⁻¹ * g * S.xβ) • S.D.alpha 0 = S.D.alpha 0 ∧
      (S.xβ⁻¹ * g * S.xβ) • S.D.alpha 2 = S.D.alpha 2 := by
  have hfix := (Arc.mem_stab G).1 hg
  have hα : g • S.α = S.α := by
    have := hfix 0 (by norm_num)
    rwa [S.D.start 2] at this
  have hβ : g • S.beta = S.beta := hfix 1 (by norm_num)
  have hα2 : g • S.D.alpha 2 = S.D.alpha 2 := hfix 2 (by norm_num)
  have hδ2 : g • S.D.delta 2 = S.D.delta 2 := hfix 4 (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [mul_smul, mul_smul, S.f95_xβ_smul_alpha0, hδ2, S.xβ_inv_smul_delta2]
  · rw [mul_smul, mul_smul, S.f95_xβ_smul_alpha2, S.f95_fix_third F hα hβ hα2,
      S.xβ_inv_smul_xβ_inv_alpha]

theorem f95_fixes_path (F : FanTree Γ G) {g : G} (hg : g ∈ (S.D.P 2).stab G) :
    ∀ v ∈ pathSet Γ (S.D.alpha 2) (S.D.alpha 0), (S.xβ⁻¹ * g * S.xβ) • v = v := fun _ hv =>
  fixes_pathSet F (S.f95_psi_fixes F hg).2 (S.f95_psi_fixes F hg).1 hv

theorem f95_w_mem_stab : S.w ∈ (S.D.P 2).stab G := S.isW1.fixes

theorem f95_c_mem_stab (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) :
    S.c ∈ (S.D.P 2).stab G :=
  (Arc.mem_stab G).2 fun _ hm => S.D.fix_of_mem_calpha F h71a h71c S.c_mem_calpha 2 hm

theorem f95_wA_fixes_path (F : FanTree Γ G) :
    ∀ v ∈ pathSet Γ (S.D.alpha 2) (S.D.alpha 0), S.wA 1 • v = v := by
  rw [S.f95_wA_eq]
  exact S.f95_fixes_path F S.f95_w_mem_stab

theorem f95_cA_fixes_path (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) :
    ∀ v ∈ pathSet Γ (S.D.alpha 2) (S.D.alpha 0), S.cA 1 • v = v := by
  rw [S.f95_cA_eq]
  exact S.f95_fixes_path F (S.f95_c_mem_stab F h71a h71c)

theorem f95_wA_orderOf (F : FanTree Γ G) (h71c : Fan71c F L) : orderOf (S.wA 1) = 4 := by
  have := (MulAut.conj S.xβ⁻¹).orderOf_eq S.w
  rw [S.psi_apply] at this
  rw [S.f95_wA_eq, this]
  exact S.orderOf_w F h71c

theorem f95_cA_orderOf (hc4 : Nat.card S.D.calpha = 4) : orderOf (S.cA 1) = 4 := by
  have := (MulAut.conj S.xβ⁻¹).orderOf_eq S.c
  rw [S.psi_apply] at this
  rw [S.f95_cA_eq, this, ← Nat.card_zpowers, ← S.gen, hc4]

theorem f95_zNb_one (F : FanTree Γ G) (h512 : Fan512 F L) :
    S.zNb 1 = S.zMu1 2 * L.z S.α := by
  have h := S.zNb_one_mul_alpha F h512
  rw [S.zNb_two] at h
  have hz : L.z S.α * L.z S.α = 1 := L.z_mul_self S.D.val
  calc S.zNb 1 = S.zNb 1 * (L.z S.α * L.z S.α) := by rw [hz, mul_one]
    _ = (S.zNb 1 * L.z S.α) * L.z S.α := by rw [mul_assoc]
    _ = S.zMu1 2 * L.z S.α := by rw [h]; rfl

theorem f95_wA_sq_one (F : FanTree Γ G) (h512 : Fan512 F L)
    (hsq : S.w * S.w = S.zEta13 * L.z S.α) :
    S.wA 1 * S.wA 1 = S.zMu1 0 * S.zMu1 2 * L.z S.α := by
  have h : S.wA 1 * S.wA 1 = MulAut.conj S.xβ⁻¹ (S.w * S.w) := by
    rw [S.f95_wA_eq, S.psi_apply]
    group
  rw [h, hsq, map_mul, show S.zEta13 = S.zMu 2 from S.zMu_two.symm, S.psi_zMu_two F,
    S.psi_zalpha, S.f95_zNb_one F h512, S.zMu_zero, mul_assoc]
  rfl

theorem f95_wA_sq_zero (F : FanTree Γ G) (hsq : S.w * S.w = S.zEta13) :
    S.wA 1 * S.wA 1 = S.zMu1 0 := by
  have h : S.wA 1 * S.wA 1 = MulAut.conj S.xβ⁻¹ (S.w * S.w) := by
    rw [S.f95_wA_eq, S.psi_apply]
    group
  rw [h, hsq, show S.zEta13 = S.zMu 2 from S.zMu_two.symm, S.psi_zMu_two F, S.zMu_zero]
  rfl

theorem f95_cA_sq (F : FanTree Γ G) (h71c : Fan71c F L) (h512 : Fan512 F L)
    (hc4 : Nat.card S.D.calpha = 4) :
    S.cA 1 * S.cA 1 = S.zMu1 2 * L.z S.α := by
  have h : S.cA 1 * S.cA 1 = MulAut.conj S.xβ⁻¹ (S.c * S.c) := by
    rw [S.f95_cA_eq, S.psi_apply]
    group
  have hc2 : S.c * S.c = L.z S.α := by
    rw [← pow_two]
    exact S.D.sq_eq_z_of_card_four F h71c h512 S.gen hc4
  rw [h, hc2, S.psi_zalpha, S.f95_zNb_one F h512]

end Sec9Cfg

end CFSG.Quasithin.Fan86

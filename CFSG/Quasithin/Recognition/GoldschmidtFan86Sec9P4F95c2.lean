module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95c
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem yMu_prod_fcomm (F : FanTree Γ G) (h71c : Fan71c F L) (h83b : Fan83b F L)
    (h83d : Fan83d F L) (h512 : Fan512 F L)
    (hR : P1Rel S.D.x S.w (L.z S.α) S.yEta S.zMu1) :
    S.yMu 0 * S.yMu 1 * S.yMu 2 = 1 ∧
      fcomm (S.yMu 2) S.t = L.z (S.D.alpha 3) * L.z (S.D.alpha 4) * L.z S.α := by
  obtain ⟨e, he⟩ := S.fcomm_yMu_two_t F h71c h83d
  have hY3 := S.yMu_two_mul_self F h71c
  have hY2 := S.yMu_one_mul_self F h71c
  have hY1 := S.yMu_zero_mul_self F h71c
  have hY3i : (S.yMu 2)⁻¹ = S.yMu 2 := inv_eq_of_mul_eq_one_right hY3
  have hY2i : (S.yMu 1)⁻¹ = S.yMu 1 := inv_eq_of_mul_eq_one_right hY2
  have htinv := S.t_inv h71c
  have hn := S.zNb_one_mul_self F
  have hne : S.zNb 1 ≠ L.z S.α := fun h' => by
    rw [S.zNb_one] at h'
    exact S.alpha_ne_xβ_inv (h71c.z_injective ((valence_smul F S.xβ⁻¹ S.α).trans S.D.val)
      S.D.val h')
  have he1 : S.yMu 2 * (S.yMu 1 * S.zNb 1) = L.z (S.D.alpha 3) * L.z (S.D.alpha 4) *
      L.z S.α ^ (e : ℕ) := by
    have h1 : fcomm (S.yMu 2) S.t = S.yMu 2 * (S.t * S.yMu 2 * S.t) := by
      unfold fcomm
      rw [hY3i, htinv]
      group
    rw [← S.t_conj_yMu_two F h71c h83b, ← h1]
    exact he
  have he2 : S.yMu 2 * S.yMu 1 = L.z (S.D.alpha 3) * L.z (S.D.alpha 4) * L.z S.α ^ (e : ℕ) *
      S.zNb 1 := by
    calc S.yMu 2 * S.yMu 1 = S.yMu 2 * (S.yMu 1 * (S.zNb 1 * S.zNb 1)) := by rw [hn, mul_one]
      _ = (S.yMu 2 * (S.yMu 1 * S.zNb 1)) * S.zNb 1 := by group
      _ = _ := by rw [he1]
  rw [S.zNb_one_eq F h71c h512] at he2
  have hz1 := S.yMu_zero_eq_zMu1
  obtain rfl | rfl : e = 0 ∨ e = 1 := by fin_cases e <;> simp
  · exfalso
    have hP : S.yMu 2 * S.yMu 1 = S.zMu1 0 * S.zMu1 1 * L.z S.α := by
      rw [he2]
      simp only [Fin.val_zero, pow_zero]
      show S.zMu1 3 * S.zMu1 4 * 1 * (L.z S.α * S.zMu1 2) = _
      coll hR
    have hP' : S.yMu 1 * S.yMu 2 = S.zMu1 0 * S.zMu1 1 * L.z S.α := by
      have : S.yMu 1 * S.yMu 2 = (S.yMu 2 * S.yMu 1)⁻¹ := by rw [mul_inv_rev, hY2i, hY3i]
      rw [this, hP]
      simp only [mul_inv_rev, P1Rel.z_inv hR, P1Rel.za_inv hR]
      coll hR
    have hd : S.yMu 0 * S.yMu 1 * S.yMu 2 = L.z S.α := by
      rw [mul_assoc, hP', hz1]
      coll hR
    have hψ := congrArg (MulAut.conj S.xβ⁻¹) hd
    rw [map_mul, map_mul, S.psi_yMu_zero F, S.psi_yMu_one F, S.psi_yMu_two F, S.psi_zalpha] at hψ
    apply hne
    rw [← hψ, hP', hz1]
    coll hR
  · have hP : S.yMu 2 * S.yMu 1 = S.zMu1 0 * S.zMu1 1 := by
      rw [he2]
      simp only [Fin.val_one, pow_one]
      show S.zMu1 3 * S.zMu1 4 * L.z S.α * (L.z S.α * S.zMu1 2) = _
      coll hR
    have hP' : S.yMu 1 * S.yMu 2 = S.zMu1 0 * S.zMu1 1 := by
      have : S.yMu 1 * S.yMu 2 = (S.yMu 2 * S.yMu 1)⁻¹ := by rw [mul_inv_rev, hY2i, hY3i]
      rw [this, hP]
      simp only [mul_inv_rev, P1Rel.z_inv hR]
      coll hR
    refine ⟨?_, by simpa using he⟩
    rw [mul_assoc, hP', hz1]
    coll hR

theorem yMu_prod_eq_one (F : FanTree Γ G) (h71c : Fan71c F L) (h83b : Fan83b F L)
    (h83d : Fan83d F L) (h512 : Fan512 F L)
    (hR : P1Rel S.D.x S.w (L.z S.α) S.yEta S.zMu1) :
    S.yMu 0 * S.yMu 1 * S.yMu 2 = 1 :=
  (S.yMu_prod_fcomm F h71c h83b h83d h512 hR).1

end Sec9Cfg

theorem fan_9_5c (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h82 : Fan82 F L)
    (h83 : Fan83 F L) (h85 : Fan85 F L) (h512 : Fan512 F L) : Fan95c F L := fun S =>
  S.yMu_prod_eq_one F h7.2.2.1 h83.2.1 h83.2.2.2.1 h512
    (S.p1Rel_of F h7.2.2.1 h82.1 h83.2.1 h83.2.2.2.1 h85)

end CFSG.Quasithin.Fan86
